/-
The problem is originally presented in:
A. Pease, G. Sutcliffe, N. Siegel, and S. Trac, “Large Theory
Reasoning with SUMO at CASC,” pp. 1–8, Jul. 2009.
Here we present the natural deduction proof in Lean.
-/

constant U : Type

constants SetOrClass Set Class Object Entity NullList_m List : U
constants CorpuscularObject Invertebrate Vertebrate Animal SpinalColumn : U
constants exhaustiveDecomposition3 disjointDecomposition3 partition3 : U → U → U → Prop
constants Organism Agent Physical : U
constants subclass_m TransitiveRelation PartialOrderingRelation: U

constant BananaSlug10 : U

constant ins : U → U → Prop 
constant subclass : U → U → Prop
constant disjoint : U → U → Prop
constant component : U → U → Prop
constant part : U → U → Prop
constant inList : U → U → Prop
constant ConsFn : U → U → U
constant ListFn1 : U → U
constant ListFn2 : U → U → U
constant ListFn3 : U → U → U → U
constant PartialOrderingRelation2 : (U → U → Prop) → Prop


/- SUMO axioms -/

variable a72771 : ins Animal SetOrClass

-- axiom1
variable a72772 : ins BananaSlug10 Animal
variable a72778 : ins Invertebrate SetOrClass

/-
axiom2 (edited see https://github.com/own-pt/cl-krr/issues/23)
variable a72773 : ∀ a : U, ∃ p : U, ins p Object ∧ 
 (ins a Animal ∧ ¬ (ins p SpinalColumn ∧ part p a) → ¬ ins a Vertebrate) 
-/
variable a72773 : ∀ a : U, ((ins a Animal) ∧ (¬ ∃ p : U, ins p SpinalColumn ∧ part p a)) 
  → ¬ ins a Vertebrate

/-
(forall (?SPINE)
 (=> (instance ?SPINE Object)
  (not (and (instance ?SPINE SpinalColumn) (part ?SPINE BananaSlug10)))))
fof(a72774,axiom,! [SPINE] : ((s_instance(SPINE, s_Object) => 
 (~ (s_instance(SPINE, s_SpinalColumn) & s_part(SPINE, s_BananaSlug10)))))).
-/
--variable a72774 : ¬ ∃ s : U, ins s SpinalColumn ∧ part s BananaSlug10
variable a72774 : ∀ s : U, ins s Object → ¬ (ins s SpinalColumn ∧ part s BananaSlug10)

variable a72761 : ∀ x row0 row1 : U, ins row0 Entity ∧ ins row1 Entity ∧ ins x Entity → 
 ListFn3 x row0 row1 = ConsFn x (ListFn2 row0 row1)

variable a72767 : ∀ x y : U, (ins x Entity ∧ ins y Entity) → 
 (ListFn2 x y) = (ConsFn x (ConsFn y NullList_m))

variable a72768 : ∀ x : U, ins x Entity → 
 (ListFn1 x = ConsFn x NullList_m)

variable a72769 : ∀ x : U, ins x Entity → 
 ¬ inList x NullList_m  

variable a72770 : ∀ L x y : U, (ins x Entity ∧ ins y Entity ∧ ins L List) → 
 (inList x (ConsFn y L)) ↔ ((x = y) ∨ inList x L)

variable a67331 : ins Entity SetOrClass
variable a67958 : ins List SetOrClass  
variable a67959 : ins NullList_m List


/-
(instance Vertebrate SetOrClass)
fof(a71402,axiom,s_instance(s_Vertebrate, s_SetOrClass)).
-/
variable a71402 : ins Vertebrate SetOrClass 

/-
(instance Animal SetOrClass)
fof(a71402,axiom,s_instance(s_Animal, s_SetOrClass)).
-/
variable a71403 : ins Animal SetOrClass

/-
(instance Organism SetOrClass)
fof(a71390,axiom,s_instance(s_Organism, s_SetOrClass)).
-/ 
variable a71390 : ins Organism SetOrClass

/-
(instance Agent SetOrClass)
fof(a71894,axiom,s_instance(s_Agent, s_SetOrClass)).
-/
variable a71894 : ins Agent SetOrClass

/-
(instance Object SetOrClass)
fof(a71691,axiom,s_instance(s_Object, s_SetOrClass)).
-/
variable a71691 : ins Object SetOrClass


/-
(instance Physical SetOrClass)
fof(a69782,axiom,s_instance(s_Physical, s_SetOrClass)).
-/
variable a69782 : ins Physical SetOrClass

/-
(instance Entity SetOrClass)
fof(a67331,axiom,s_instance(s_Entity, s_SetOrClass)).
-/
variable a67332 : ins Entity SetOrClass

-- axPVI
variable a71370 : partition3 Animal Vertebrate Invertebrate

-- axPartition
variable a67131 : ∀ c row0 row1 : U, (ins row0 Class ∧ ins c Class ∧ ins row1 Class) → 
 partition3 c row0 row1 ↔ (exhaustiveDecomposition3 c row0 row1 ∧ disjointDecomposition3 c row0 row1)

-- axExDec
variable a67963 : ∀ row0 row1 row2 c : U, (∀ obj : U, (∃ item : U, ins item SetOrClass ∧ ins obj Entity → 
 (ins c SetOrClass ∧ ins c Class ∧ ins row1 Class ∧ ins row1 Entity ∧ ins row0 Class ∧ ins row0 Entity ∧ ins row2 Entity) → 
 exhaustiveDecomposition3 c row0 row1 → ins obj Class → inList item (ListFn3 row0 row1 row2) ∧ ins obj item))

-- axExDec (manual edited see https://github.com/own-pt/cl-krr/issues/22)
variable a67115 : ∀ row1 row0 c : U, ∀ obj : U, ∃ item : U, ins item SetOrClass ∧ 
 (ins obj Entity → 
  ((ins c SetOrClass ∧ ins c Class ∧ ins row1 Class ∧ ins row1 Entity ∧ ins row0 Class ∧ ins row0 Entity) →   
   (exhaustiveDecomposition3 c row0 row1 → (ins obj c → (inList item (ListFn2 row0 row1) ∧ ins obj item)))))

/-
(partition3 SetOrClass Set Class)
fof(a67447,axiom,s_partition3(s_SetOrClass, s_Set, s_Class)).
-/
variable a67447 : partition3 SetOrClass Set Class 

/-
(subclass Vertebrate Animal)
fof(a71382,axiom,s_subclass(s_Vertebrate, s_Animal)).
-/
variable a71382 : subclass Vertebrate Animal

/-
(subclass Invertebrate Animal)
fof(a71383,axiom,s_subclass(s_Invertebrate, s_Animal)).
-/
variable a71383 : subclass Invertebrate Animal

-- REDUNDANT (see https://github.com/own-pt/cl-krr/issues/24) ON TPTP TRANSLATION
/-
(forall (?Y ?X)
 (=> (and (instance ?Y SetOrClass) (instance ?X SetOrClass))
  (=> (subclass ?X ?Y)
   (and (instance ?X SetOrClass) (instance ?Y SetOrClass)))))
fof(a14,axiom,! [Y,X] : (((s_instance(Y, s_SetOrClass) & s_instance(X, s_SetOrClass)) => (s_subclass(X, Y) =>
 (s_instance(X, s_SetOrClass) & s_instance(Y, s_SetOrClass)))))).
-/
variable a14 : ∀ x y : U, subclass x y → ins x SetOrClass ∧ ins y SetOrClass 

/-
(forall (?Y ?Z ?X)
 (=> (and (instance ?X SetOrClass) (instance ?Y SetOrClass))
  (=> (and (subclass ?X ?Y) (instance ?Z ?X)) 
      (instance ?Z ?Y))))
fof(a15,axiom,! [Y,Z,X] : (((s_instance(X, s_SetOrClass) & s_instance(Y, s_SetOrClass)) => ((s_subclass(X, Y) & s_instance(Z, X)) => s_instance(Z, Y))))).
-/
variable a15 : ∀ x y z : U, ins x SetOrClass ∧ ins y SetOrClass → (subclass x y ∧ ins z x → ins z y)
--variable a16 : ∀ x y z : U, partition3 x y z → ins x Class ∧ ins y Class ∧ ins z Class 

/-
(exists (?THING) (instance ?THING Entity))
fof(a67172,axiom,? [THING] : (s_instance(THING, s_Entity))).
-/
variable a67172 : ∃ x : U, ins x Entity

/-
(forall (?CLASS) (<=> (instance ?CLASS Class) (subclass ?CLASS Entity)))
fof(a67173,axiom,! [CLASS] : ((s_instance(CLASS, s_Class) <=> s_subclass(CLASS, s_Entity)))).
-/
variable a67173 : ∀ c : U, ins c Class ↔ subclass c Entity

/-
(instance TransitiveRelation SetOrClass)
fof(a71866,axiom,s_instance(s_TransitiveRelation, s_SetOrClass)).
-/
variable a71866 : ins TransitiveRelation SetOrClass

/-
(instance PartialOrderingRelation SetOrClass)
fof(a72202,axiom,s_instance(s_PartialOrderingRelation, s_SetOrClass)).
-/
variable a72202 : ins PartialOrderingRelation SetOrClass

/-
(instance subclass PartialOrderingRelation)
fof(a13,axiom,s_instance(s_subclass_m, s_PartialOrderingRelation)).
-/
variable a13 : ins subclass_m PartialOrderingRelation

/-
(subclass PartialOrderingRelation TransitiveRelation)
fof(a67817,axiom,s_subclass(s_PartialOrderingRelation, s_TransitiveRelation)).
-/
variable a67817 : subclass PartialOrderingRelation TransitiveRelation

/-
(forall (?Y ?Z ?X)
 (=> (and (instance ?X SetOrClass) (instance ?Y SetOrClass))
  (=> (and (subclass ?X ?Y) (instance ?Z ?X)) (instance ?Z ?Y))))
fof(a15,axiom,! [Y,Z,X] : (((s_instance(X, s_SetOrClass) & s_instance(Y, s_SetOrClass)) => ((s_subclass(X, Y) & s_instance(Z, X)) => s_instance(Z, Y))))).
-/
variable a16: ∀ x y z : U, ins x SetOrClass ∧ ins y SetOrClass → subclass x y ∧ ins z x → ins z y

/-
(forall (?INST1 ?INST2 ?INST3)
 (=>
  (and (instance ?INST2 SetOrClass) (instance ?INST1 SetOrClass)
   (instance ?INST3 SetOrClass))
  (=> (instance subclass TransitiveRelation)
   (=> (and (subclass ?INST1 ?INST2) (subclass ?INST2 ?INST3))
    (subclass ?INST1 ?INST3)))))
fof(a67808,axiom,! [INST1,INST2,INST3] : (((s_instance(INST2, s_SetOrClass) & s_instance(INST1, s_SetOrClass) & s_instance(INST3, s_SetOrClass)) => (s_instance(s_subclass_m, s_TransitiveRelation) => ((s_subclass(INST1, INST2) & s_subclass(INST2, INST3)) => s_subclass(INST1, INST3)))))).
-/
variable a67808 : ∀ x y z : U, ins x SetOrClass ∧ ins y SetOrClass ∧ ins z SetOrClass → ins subclass_m TransitiveRelation → 
  (subclass x y ∧ subclass y z → subclass x z)

/-
(subclass Animal Organism)
fof(a71388,axiom,s_subclass(s_Animal, s_Organism)).
-/
variable a71388 : subclass Animal Organism

/-
(subclass Organism Agent)
fof(a71359,axiom,s_subclass(s_Organism, s_Agent)).
-/
variable a71359 : subclass Organism Agent

/-
(subclass Agent Object)
fof(a67315,axiom,s_subclass(s_Agent, s_Object)).
-/
variable a67315 : subclass Agent Object

/-
(subclass Object Physical)
fof(a67177,axiom,s_subclass(s_Object, s_Physical)).
-/
variable a67177 : subclass Object Physical

/-
(subclass Physical Entity)
fof(a67174,axiom,s_subclass(s_Physical, s_Entity)).
-/
variable a67174 : subclass Physical Entity



-- starting proofs

include a67173 a71382 a71388 a67817 a13 a71359 a67315 a67177 a67174 a16 a71866 a72202 a67808 a71402 a71403 a71390 a71894 a71691 a69782 a67332

lemma la (hne : nonempty U) : subclass Vertebrate Entity :=
begin
  have h, exact ((a16 PartialOrderingRelation TransitiveRelation subclass_m) (and.intro a72202 a71866)) (and.intro a67817 a13),
  have h₂, from (a67808 Vertebrate Animal Organism) (and.intro a71402 (and.intro a71403 a71390)) h (and.intro a71382 a71388),
  have h₃, from (a67808 Vertebrate Organism Agent) (and.intro a71402 (and.intro a71390 a71894)) h (and.intro h₂ a71359),
  have h₄, from (a67808 Vertebrate Agent Object) (and.intro a71402 (and.intro a71894 a71691)) h (and.intro h₃ a67315),
  have h₅, from (a67808 Vertebrate Object Physical) (and.intro a71402 (and.intro a71691 a69782)) h (and.intro h₄ a67177),
  have h₆, from (a67808 Vertebrate Physical Entity) (and.intro a71402 (and.intro a69782 a67332)) h (and.intro h₅ a67174),
  exact h₆
end

lemma l1 (hne : nonempty U) : subclass Vertebrate Entity :=
begin
  --have h₁, from (a15 Vertebrate) Animal,
  have h₁, from and.intro a71382 a71388,
--  specialize a67817 subclass,
  have h₂, from a67817 a13,
  have h₃, from h₂ Vertebrate Animal Organism,
  have h₄, from h₃ (and.intro a71382 a71388),
  have h₅, from (h₂ Vertebrate Organism Agent) (and.intro h₄ a71359),
  have h₆ , from (h₂ Vertebrate Agent Object) (and.intro h₅ a67315),
  have h₇ , from (h₂ Vertebrate Object Physical) (and.intro h₆  a67177),
  have h₈ , from (h₂ Vertebrate Physical Entity) (and.intro h₇  a67174),
  exact h₈
end

include a72772 a72773 a72774

lemma BS10notVert (hne : nonempty U) : ¬(ins BananaSlug10 Vertebrate) :=
begin
 have h₁, from and.intro a72772 a72774,
 have h₂, from a72773 BananaSlug10,
 have h₃, from h₂ h₁,
 exact h₃
end

omit a72772 a72773 a72774


include a67131 a72778 a71370 a71402 a72771 a15

lemma l1 (hne : nonempty U) : ins Vertebrate Class :=
begin
 have h₁, from (a15 Vertebrate) Animal,

end

lemma BS10VI (hne : nonempty U) : ins BananaSlug10 Vertebrate ∨ ins BananaSlug10 Invertebrate :=
begin
 have h₁, from ((a67131 Animal) Vertebrate) Invertebrate,
 
end



-- draft

-- tem como provar?
variable axiom4 : ¬ (Vertebrate = Invertebrate) 


variable axDisDec : ∀ ac y z : U, 
 disjointDecomposition ac y z → 
   (∀ i1 i2 : U, 
    (list.mem i1 (y :: z :: []) ∧ list.mem i2 (y :: z :: []) ∧ ¬ (i1 = i2)) →
    (disjoint i1 i2))

variable axDisjoint : ∀ c1 c2 : U,
 disjoint c1 c2 → ∀ i : U, ¬ (ins i c1 ∧ ins i c2)

-- variable axEqual : ∀ c1 c2 : U, equal c1 c2 → ∀ t : U, (ins t c1 ↔ ins t c2)

lemma vertInvert : ∀ x : U, ins x Vertebrate → ¬ ins x Invertebrate :=
λ x : U,
  λ h: ins x Vertebrate,
    have h₁: disjointDecomposition Animal Vertebrate Invertebrate, 
      from ((axPartition Animal Vertebrate Invertebrate).mp axPVI).right,
    have h₂: disjoint Vertebrate Invertebrate, 
      from (((axDisDec Animal Vertebrate Invertebrate) h₁) Vertebrate Invertebrate) 
           (and.intro (or.inl (eq.refl Vertebrate)) (and.intro (or.inr (or.inl (eq.refl Invertebrate))) axiom4)),
    λ h₃ : ins x Invertebrate,
      show false, from (((axDisjoint Vertebrate Invertebrate) h₂) x) (and.intro h h₃)


lemma BS10inList : ∃ c : U, (list.mem c [Vertebrate, Invertebrate]) ∧ (ins BananaSlug10 c) :=
have h₁ : exhaustiveDecomposition Animal Vertebrate Invertebrate, 
  from (and.left((iff.mp (axPartition Animal Vertebrate Invertebrate)) axPVI)),
have h₂ : (∀ o : U, (ins o Animal) → ∃ i : U, (list.mem i [Vertebrate, Invertebrate]) ∧ ins o i),
  from (axExDec Animal Vertebrate Invertebrate) h₁,
(h₂ BananaSlug10) axiom1


lemma BS10VI : (ins BananaSlug10 Vertebrate ∨ ins BananaSlug10 Invertebrate) :=
exists.elim (BS10inList axiom1 axPVI axPartition axExDec)
 (λ x : U,
   λ hx : (list.mem x [Vertebrate, Invertebrate]) ∧ (ins BananaSlug10 x),
     or.elim hx.left 
       (λ h₁ : x = Vertebrate,
         have h₂ : ins BananaSlug10 Vertebrate, from eq.subst h₁ hx.right,
         or.inl h₂)
       (λ h₁ : list.mem x [Invertebrate],
         or.elim h₁ 
           (λ h₂ : x = Invertebrate,
             have h₂ : ins BananaSlug10 Invertebrate, from eq.subst h₂ hx.right,
             or.inr h₂) 
           (λ h₂ : list.mem x [], false.elim h₂)))


theorem goal : ins BananaSlug10 Invertebrate :=
or.elim (BS10VI axiom1 axPVI axPartition axExDec) 
  (λ h : ins BananaSlug10 Vertebrate,
    have hf : false, from (BS10notVert axiom1 axiom2 axiom3) h,
    false.elim hf)
  (λ h : ins BananaSlug10 Invertebrate, h)
