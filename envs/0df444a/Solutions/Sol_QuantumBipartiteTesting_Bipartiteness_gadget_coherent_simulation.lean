-- Prove2me | solution 1 for QuantumBipartiteTesting.Bipartiteness.gadget_coherent_simulation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T13:32:08.799077+00:00
-- url     : https://prove2.me/submissions/5dd78b21-f4e7-4db6-ac3e-794babbd2610

import Definitions.Def_QuantumBipartiteTesting_Bipartiteness_Reduction

namespace QuantumBipartiteTesting.Bipartiteness
noncomputable section
open Finset
attribute [local instance] Classical.propDecidable Classical.decEq
set_option maxHeartbeats 1000000
set_option maxRecDepth 2000

private def PermU {S : Type*} [Fintype S] [DecidableEq S] (p : Equiv.Perm S) : Matrix.unitaryGroup S ℂ :=
  ⟨(p⁻¹).permMatrix ℂ, by
    rw [Matrix.mem_unitaryGroup_iff]
    change (p⁻¹).permMatrix ℂ * ((p⁻¹).permMatrix ℂ).conjTranspose = 1
    rw [Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul]
    simp⟩

private lemma perm_embed {S T : Type*} [Fintype S] [Fintype T] [DecidableEq T]
    (p : Equiv.Perm T) (e : S → T) (ψ : S → ℂ) :
    (PermU p : Matrix T T ℂ).mulVec (EmbedState e ψ) =
      EmbedState (fun s => p (e s)) ψ := by
  rw [show (PermU p : Matrix T T ℂ) = (p⁻¹).permMatrix ℂ from rfl,
    Matrix.permMatrix_mulVec]
  ext t
  simp only [EmbedState, Function.comp_apply]
  apply sum_congr rfl
  intro s hs
  have hh : e s = p.symm t ↔ p (e s) = t := by
    constructor
    · intro h; rw [h]; exact p.apply_symm_apply t
    · intro h; rw [← h]; exact (p.symm_apply_apply (e s)).symm
  simp only [Equiv.Perm.inv_def, hh]
  split_ifs <;> rfl

private def QueryPerm {I B W : Type*} [AddCommGroup B]
    (f : I → B) : Equiv.Perm ((I × B) × W) where
  toFun s := ((s.1.1,s.1.2 + f s.1.1),s.2)
  invFun s := ((s.1.1,s.1.2 - f s.1.1),s.2)
  left_inv s := by simp
  right_inv s := by simp

private lemma query_matrix {I B W : Type*} [Fintype I] [Fintype B] [Fintype W]
    [DecidableEq I] [DecidableEq B] [DecidableEq W] [AddCommGroup B] (f : I → B) :
    Matrix.kronecker (QAlgorithms.xorOracle f) (1 : Matrix W W ℂ) =
      (PermU (QueryPerm (W := W) f) : Matrix _ _ ℂ) := by
  ext s t
  rcases s with ⟨⟨i,a⟩,u⟩
  rcases t with ⟨⟨j,b⟩,v⟩
  simp only [Matrix.kronecker, Matrix.kroneckerMap_apply, QAlgorithms.xorOracle, Matrix.of_apply,
    Matrix.one_apply, PermU, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
    Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq]
  change (if i = j ∧ a = b + f j then 1 else 0) * (if u = v then 1 else 0) =
    (if ((i,a-f i),u) = ((j,b),v) then (1 : ℂ) else 0)
  have hh : ((j,b),v) = ((i,a-f i),u) ↔ (i = j ∧ a = b+f j) ∧ u = v := by
    simp only [Prod.mk.injEq]
    constructor
    · rintro ⟨⟨rfl,h⟩,rfl⟩
      exact ⟨⟨rfl,(eq_sub_iff_add_eq.mp h).symm⟩,rfl⟩
    · rintro ⟨⟨rfl,rfl⟩,rfl⟩
      simp
  simp only [show (((i,a-f i),u) = ((j,b),v)) ↔ (i = j ∧ a = b+f j) ∧ u = v from eq_comm.trans hh]
  split_ifs <;> simp_all

private lemma permU_mul {S : Type*} [Fintype S] [DecidableEq S] (p r : Equiv.Perm S) :
    (PermU r : Matrix S S ℂ) * (PermU p : Matrix S S ℂ) =
      (PermU (p.trans r) : Matrix S S ℂ) := by
  change (r⁻¹).permMatrix ℂ * (p⁻¹).permMatrix ℂ = _
  rw [← Matrix.permMatrix_mul]
  rfl

private abbrev Word (S : Type*) := List (Sum (Equiv.Perm S) Unit)

private def WordPerm {S : Type*} (Q : Equiv.Perm S) : Word S → Equiv.Perm S
  | [] => Equiv.refl S
  | Sum.inl p :: gs => p.trans (WordPerm Q gs)
  | Sum.inr _ :: gs => Q.trans (WordPerm Q gs)

private def Realize {n k w : ℕ} (word : Word (SimulationBasis n k w)) :
    List (SimulationGate n k w) := word.map (Sum.map PermU id)

private lemma realize_matrix {n k w : ℕ} (f : Address n 3 → Bits k)
    (word : Word (SimulationBasis n k w)) :
    CircuitMatrix (QAlgorithms.xorOracle f) (Realize word) =
      (PermU (WordPerm (QueryPerm f) word) : Matrix _ _ ℂ) := by
  induction word with
  | nil =>
    change (1 : Matrix (SimulationBasis n k w) (SimulationBasis n k w) ℂ) =
      (PermU (Equiv.refl (SimulationBasis n k w)) : Matrix _ _ ℂ)
    change (1 : Matrix _ _ ℂ) = ((1 : Equiv.Perm (SimulationBasis n k w))⁻¹).permMatrix ℂ
    simp
  | cons g gs ih =>
    cases g with
    | inl p =>
      change CircuitMatrix (QAlgorithms.xorOracle f) (Realize gs) * (PermU p : Matrix _ _ ℂ) = _
      rw [ih]
      exact permU_mul p (WordPerm (QueryPerm f) gs)
    | inr u =>
      change CircuitMatrix (QAlgorithms.xorOracle f) (Realize gs) *
        Matrix.kronecker (QAlgorithms.xorOracle f) (1 : Matrix (Fin w) (Fin w) ℂ) = _
      rw [ih, query_matrix]
      exact permU_mul (QueryPerm (W := Fin w) f) (WordPerm (QueryPerm f) gs)

private lemma wordPerm_append {S : Type*} (Q : Equiv.Perm S) (a b : Word S) :
    WordPerm Q (a ++ b) = (WordPerm Q a).trans (WordPerm Q b) := by
  induction a with
  | nil => rfl
  | cons g gs ih =>
    cases g <;> simp only [List.cons_append, WordPerm, ih, Equiv.trans_assoc]

private def Conjugate {S T : Type*} (e : S ≃ T) (p : Equiv.Perm S) : Equiv.Perm T :=
  e.symm.trans (p.trans e)

private lemma conjugate_apply {S T : Type*} (e : S ≃ T) (p : Equiv.Perm S) (s : S) :
    Conjugate e p (e s) = e (p s) := by simp [Conjugate]

private lemma conjugate_trans {S T : Type*} (e : S ≃ T) (p r : Equiv.Perm S) :
    Conjugate e (p.trans r) = (Conjugate e p).trans (Conjugate e r) := by
  ext t
  simp [Conjugate]

private def TransportWord {S T : Type*} (e : S ≃ T) (word : Word S) : Word T :=
  word.map (Sum.map (Conjugate e) id)

private lemma transport_wordPerm {S T : Type*} (e : S ≃ T)
    (Q : Equiv.Perm S) (R : Equiv.Perm T) (hQ : Conjugate e Q = R) (word : Word S) :
    WordPerm R (TransportWord e word) = Conjugate e (WordPerm Q word) := by
  induction word with
  | nil => ext t; simp [TransportWord, WordPerm, Conjugate]
  | cons g gs ih =>
    dsimp only [TransportWord] at ih
    cases g <;> simp only [TransportWord, List.map_cons, Sum.map_inl, Sum.map_inr,
      WordPerm, ih, conjugate_trans, hQ]

private lemma memory_query_conjugate {I B W Z : Type*} [AddCommGroup B]
    (e : W ≃ Z) (f : I → B) :
    Conjugate (Equiv.prodCongr (Equiv.refl (I × B)) e) (QueryPerm f) = QueryPerm f := by
  ext s <;> simp [Conjugate, QueryPerm]

private abbrev Memory (L : Type*) (kS kT : ℕ) := (L × Bits kT) × (Fin 3 → Bits kS)
private abbrev WorkBasis (I L : Type*) (kS kT : ℕ) := (I × Bits kS) × Memory L kS kT

private def InvolPerm {S : Type*} (f : S → S) (hf : Function.Involutive f) : Equiv.Perm S :=
  ⟨f,f,hf,hf⟩

private def AddressSwap {I L : Type*} [DecidableEq I] {kS kT : ℕ}
    (i0 : I) (a : L → Fin 3 → I) (j : Fin 3) : Equiv.Perm (WorkBasis I L kS kT) :=
  InvolPerm (fun s => ((Equiv.swap i0 (a s.2.1.1 j) s.1.1,s.1.2),s.2))
    (by intro s; simp)

private def CacheSwap {I L : Type*} {kS kT : ℕ} (j : Fin 3) :
    Equiv.Perm (WorkBasis I L kS kT) :=
  InvolPerm (fun s => ((s.1.1,s.2.2 j),(s.2.1,Function.update s.2.2 j s.1.2)))
    (by intro s; simp)

private def Compute {I L : Type*} {kS kT : ℕ} (g : L → (Fin 3 → Bits kS) → Bits kT) :
    Equiv.Perm (WorkBasis I L kS kT) where
  toFun s := (s.1,((s.2.1.1,s.2.1.2+g s.2.1.1 s.2.2),s.2.2))
  invFun s := (s.1,((s.2.1.1,s.2.1.2-g s.2.1.1 s.2.2),s.2.2))
  left_inv s := by simp
  right_inv s := by simp

private def Fetch {I L : Type*} [DecidableEq I] {kS kT : ℕ}
    (i0 : I) (a : L → Fin 3 → I) (j : Fin 3) : Word (WorkBasis I L kS kT) :=
  [Sum.inl (AddressSwap i0 a j), Sum.inr (), Sum.inl (CacheSwap j), Sum.inl (AddressSwap i0 a j)]

private def Load {I L : Type*} [DecidableEq I] {kS kT : ℕ}
    (i0 : I) (a : L → Fin 3 → I) : Word (WorkBasis I L kS kT) :=
  Fetch i0 a 0 ++ Fetch i0 a 1 ++ Fetch i0 a 2

private def Seed {I L : Type*} {kS kT : ℕ} (i0 : I) (t : L × Bits kT) :
    WorkBasis I L kS kT := ((i0,0),(t,0))

private lemma fetch_apply {I L : Type*} [DecidableEq I] {kS kT : ℕ}
    (i0 : I) (a : L → Fin 3 → I) (f : I → Bits kS) (j : Fin 3)
    (t : L × Bits kT) (c : Fin 3 → Bits kS) (hc : c j = 0) :
    WordPerm (QueryPerm f) (Fetch i0 a j) ((i0,0),(t,c)) =
      ((i0,0),(t,Function.update c j (f (a t.1 j)))) := by
  simp [WordPerm, Fetch, AddressSwap, CacheSwap, InvolPerm, QueryPerm, hc]

private lemma load_apply {I L : Type*} [DecidableEq I] {kS kT : ℕ}
    (i0 : I) (a : L → Fin 3 → I) (f : I → Bits kS) (t : L × Bits kT) :
    WordPerm (QueryPerm f) (Load i0 a) (Seed i0 t) =
      ((i0,0),(t,fun j => f (a t.1 j))) := by
  simp only [Load, wordPerm_append, Equiv.trans_apply, Seed]
  rw [fetch_apply i0 a f 0 t 0 (by rfl), fetch_apply i0 a f 1 t _ (by simp),
    fetch_apply i0 a f 2 t _ (by simp)]
  congr 2
  funext j
  fin_cases j <;> simp

private def ReverseWord {S : Type*} (word : Word S) : Word S :=
  word.reverse.map (Sum.map (fun p => p⁻¹) id)

private lemma reverse_wordPerm {S : Type*} (Q : Equiv.Perm S) (hQ : Q⁻¹ = Q) (word : Word S) :
    WordPerm Q (ReverseWord word) = (WordPerm Q word)⁻¹ := by
  induction word with
  | nil => rfl
  | cons g gs ih =>
    have hr : ReverseWord (g :: gs) = ReverseWord gs ++ [Sum.map (fun p => p⁻¹) id g] := by
      simp only [ReverseWord, List.reverse_cons, List.map_append, List.map_singleton]
    rw [hr,wordPerm_append,ih]
    cases g
    · rfl
    · change ((WordPerm Q gs)⁻¹).trans Q = ((WordPerm Q gs)⁻¹).trans Q⁻¹
      exact congrArg (fun r => ((WordPerm Q gs)⁻¹).trans r) hQ.symm

private lemma bits_query_self_inverse {I W : Type*} {k : ℕ} (f : I → Bits k) :
    (QueryPerm (W := W) f)⁻¹ = QueryPerm f := by
  apply Equiv.ext
  intro s
  change ((s.1.1,s.1.2-f s.1.1),s.2) = ((s.1.1,s.1.2+f s.1.1),s.2)
  congr 1
  congr 1
  funext j
  simp [sub_eq_add_neg, ZMod.neg_eq_self_mod_two]

private def SimulationWord {I L : Type*} [DecidableEq I] {kS kT : ℕ}
    (i0 : I) (a : L → Fin 3 → I) (g : L → (Fin 3 → Bits kS) → Bits kT) :
    Word (WorkBasis I L kS kT) :=
  Load i0 a ++ [Sum.inl (Compute g)] ++ ReverseWord (Load i0 a)

private lemma simulationWord_seed {I L : Type*} [DecidableEq I] {kS kT : ℕ}
    (i0 : I) (a : L → Fin 3 → I) (g : L → (Fin 3 → Bits kS) → Bits kT)
    (f : I → Bits kS) (t : L × Bits kT) :
    WordPerm (QueryPerm f) (SimulationWord i0 a g) (Seed i0 t) =
      Seed i0 (t.1,t.2 + g t.1 (fun j => f (a t.1 j))) := by
  simp only [SimulationWord, wordPerm_append, WordPerm, Equiv.trans_apply, Equiv.refl_apply]
  rw [load_apply, reverse_wordPerm _ (bits_query_self_inverse f)]
  apply (WordPerm (QueryPerm f) (Load i0 a)).injective
  change (WordPerm (QueryPerm f) (Load i0 a))
      ((WordPerm (QueryPerm f) (Load i0 a)).symm _) = _
  rw [Equiv.apply_symm_apply, load_apply]
  rfl

private def AddPerm {I B : Type*} [AddCommGroup B] (h : I → B) : Equiv.Perm (I × B) where
  toFun s := (s.1,s.2+h s.1)
  invFun s := (s.1,s.2-h s.1)
  left_inv s := by simp
  right_inv s := by simp

private lemma xor_matrix {I B : Type*} [Fintype I] [Fintype B]
    [DecidableEq I] [DecidableEq B] [AddCommGroup B] (h : I → B) :
    QAlgorithms.xorOracle h = (PermU (AddPerm h) : Matrix _ _ ℂ) := by
  ext s t
  rcases s with ⟨i,a⟩
  rcases t with ⟨j,b⟩
  simp only [QAlgorithms.xorOracle, Matrix.of_apply, PermU, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq]
  change (if i = j ∧ a = b+h j then (1 : ℂ) else 0) =
    (if (i,a-h i) = (j,b) then 1 else 0)
  have hh : (i,a-h i) = (j,b) ↔ i = j ∧ a = b+h j := by
    simp only [Prod.mk.injEq]
    constructor
    · rintro ⟨rfl,h⟩; exact ⟨rfl,(sub_eq_iff_eq_add.mp h)⟩
    · rintro ⟨rfl,rfl⟩; simp
  simp only [hh]

private lemma embed_perm {S T : Type*} [Fintype S] [Fintype T] [DecidableEq S]
    (p : Equiv.Perm S) (e : S → T) (ψ : S → ℂ) :
    EmbedState e ((PermU p : Matrix S S ℂ).mulVec ψ) =
      EmbedState (fun s => e (p s)) ψ := by
  rw [show (PermU p : Matrix S S ℂ) = (p⁻¹).permMatrix ℂ from rfl,
    Matrix.permMatrix_mulVec]
  ext t
  change (∑ s, if e s = t then ψ (p.symm s) else 0) = _
  simpa only [EmbedState, Equiv.symm_apply_apply] using
    (Equiv.sum_comp p (fun s => if e s = t then ψ (p.symm s) else 0)).symm

private lemma realized_count {n k w : ℕ} (word : Word (SimulationBasis n k w)) :
    QueryGateCount (Realize word) = word.countP (fun g => g.isRight) := by
  simp only [QueryGateCount, Realize, List.countP_map]
  congr 1
  funext g
  cases g <;> rfl

private lemma transport_count {S T : Type*} (e : S ≃ T) (word : Word S) :
    (TransportWord e word).countP (fun g => g.isRight) = word.countP (fun g => g.isRight) := by
  simp only [TransportWord, List.countP_map]
  congr 1
  funext g
  cases g <;> rfl

private lemma reverse_count {S : Type*} (word : Word S) :
    (ReverseWord word).countP (fun g => g.isRight) = word.countP (fun g => g.isRight) := by
  simp only [ReverseWord, List.countP_map, List.countP_reverse]
  congr 1
  funext g
  cases g <;> rfl

private lemma simulation_count {I L : Type*} [DecidableEq I] {kS kT : ℕ}
    (i0 : I) (a : L → Fin 3 → I) (g : L → (Fin 3 → Bits kS) → Bits kT) :
    (SimulationWord i0 a g).countP (fun g => g.isRight) = 6 := by
  rfl

private lemma local_oracle_simulation (n kS kT : ℕ)
    (a : Address (7*n) 3 → Fin 3 → Address n 3)
    (g : Address (7*n) 3 → (Fin 3 → Bits kS) → Bits kT) :
    ∃ w : ℕ, ∃ gates : List (SimulationGate n kS w),
    ∃ embed : (Address (7*n) 3 × Bits kT) → SimulationBasis n kS w,
      Function.Injective embed ∧ QueryGateCount gates = 6 ∧
      ∀ f : Address n 3 → Bits kS, ∀ ψ : (Address (7*n) 3 × Bits kT) → ℂ,
        (CircuitMatrix (QAlgorithms.xorOracle f) gates).mulVec (EmbedState embed ψ) =
          EmbedState embed ((QAlgorithms.xorOracle (fun l => g l (fun j => f (a l j)))).mulVec ψ) := by
  let Mem := Memory (Address (7*n) 3) kS kT
  let w := Fintype.card Mem
  let me : Mem ≃ Fin w := Fintype.equivFin Mem
  let e := Equiv.prodCongr (Equiv.refl (Address n 3 × Bits kS)) me
  let i0 : Address n 3 := (none,0)
  let word := SimulationWord (kS := kS) (kT := kT) i0 a g
  let gates := Realize (TransportWord e word)
  let embed : (Address (7*n) 3 × Bits kT) → SimulationBasis n kS w :=
    fun t => e (Seed i0 t)
  refine ⟨w,gates,embed,?_,?_,?_⟩
  · intro s t h
    exact congrArg (fun u : WorkBasis (Address n 3) (Address (7*n) 3) kS kT => u.2.1)
      (e.injective h)
  · dsimp only [gates]
    rw [realized_count,transport_count,simulation_count]
  · intro f ψ
    dsimp only [gates]
    rw [realize_matrix, transport_wordPerm e (QueryPerm f) (QueryPerm f)
      (memory_query_conjugate me f), perm_embed, xor_matrix, embed_perm]
    congr 1
    funext t
    change Conjugate e (WordPerm (QueryPerm f) word) (e (Seed i0 t)) =
      e (Seed i0 (AddPerm (fun l => g l (fun j => f (a l j))) t))
    rw [conjugate_apply,simulationWord_seed]
    rfl

private def PathEdges {n : ℕ} (e : ColoredEdge n) (b : Bool) : Finset (Edge (7*n)) :=
  if b then {UEdge (Original e.1) (AuxiliaryA e.1 e.2.2),
    UEdge (AuxiliaryA e.1 e.2.2) (AuxiliaryP e.1 e.2.2),
    UEdge (AuxiliaryP e.1 e.2.2) (Original e.2.1)}
  else {UEdge (Original e.1) (AuxiliaryA e.1 e.2.2),
    UEdge (AuxiliaryA e.1 e.2.2) (Original e.2.1)}

private lemma original_lt_A {n : ℕ} (u v : Fin n) (j : Fin 3) :
    Original u < AuxiliaryA v j := by
  change u.val < n + 6*v.val + 2*j.val
  omega
private lemma original_lt_P {n : ℕ} (u v : Fin n) (j : Fin 3) :
    Original u < AuxiliaryP v j := by
  change u.val < n + 6*v.val + 2*j.val + 1
  omega
private lemma A_lt_P {n : ℕ} (u : Fin n) (j : Fin 3) :
    AuxiliaryA u j < AuxiliaryP u j := by
  change n+6*u.val+2*j.val < n+6*u.val+2*j.val+1
  omega
private lemma A_injective {n : ℕ} (u v : Fin n) (i j : Fin 3)
    (h : AuxiliaryA u i = AuxiliaryA v j) : u = v ∧ i = j := by
  have hv := congrArg Fin.val h
  simp only [AuxiliaryA] at hv
  have h1 := i.isLt
  have h2 := j.isLt
  constructor <;> apply Fin.ext <;> omega
private lemma P_injective {n : ℕ} (u v : Fin n) (i j : Fin 3)
    (h : AuxiliaryP u i = AuxiliaryP v j) : u = v ∧ i = j := by
  have hv := congrArg Fin.val h
  simp only [AuxiliaryP] at hv
  have h1 := i.isLt
  have h2 := j.isLt
  constructor <;> apply Fin.ext <;> omega
private lemma A_ne_P {n : ℕ} (u v : Fin n) (i j : Fin 3) :
    AuxiliaryA u i ≠ AuxiliaryP v j := by
  intro h
  have hv := congrArg Fin.val h
  simp only [AuxiliaryA, AuxiliaryP] at hv
  omega

private lemma uedge_lt {n : ℕ} (u v : Fin n) (h : u ≠ v) :
    (UEdge u v).1 < (UEdge u v).2 := by
  simp only [UEdge]
  exact min_lt_max.mpr h

private lemma gadget_graph {n : ℕ} (F : Finset (ColoredEdge n))
    (b : ColoredEdge n → Bool) : IsGraph (Gadget F b) := by
  intro a ha
  obtain ⟨e, he, ha⟩ := mem_biUnion.mp ha
  change a ∈ PathEdges e (b e) at ha
  cases hb : b e <;> simp only [PathEdges, hb, Bool.false_eq_true, ↓reduceIte,
    mem_insert, mem_singleton] at ha
  · rcases ha with rfl | rfl
    · exact uedge_lt _ _ (ne_of_lt (original_lt_A _ _ _))
    · exact uedge_lt _ _ (ne_of_gt (original_lt_A _ _ _))
  · rcases ha with rfl | rfl | rfl
    · exact uedge_lt _ _ (ne_of_lt (original_lt_A _ _ _))
    · exact uedge_lt _ _ (ne_of_lt (A_lt_P _ _))
    · exact uedge_lt _ _ (ne_of_gt (original_lt_P _ _ _))

private lemma proper_uedge {n : ℕ} (x : Fin n → Bool) (u v : Fin n) :
    x (UEdge u v).1 ≠ x (UEdge u v).2 ↔ x u ≠ x v := by
  by_cases h : u ≤ v
  · simp [UEdge, min_eq_left h, max_eq_right h]
  · have h' := le_of_not_ge h
    simp [UEdge, min_eq_right h', max_eq_left h', ne_comm]

private lemma path_parity {n : ℕ} (x : Fin (7*n) → Bool) (e : ColoredEdge n) (b : Bool)
    (h : ∀ a ∈ PathEdges e b, x a.1 ≠ x a.2) :
    xor (x (Original e.1)) (x (Original e.2.1)) = b := by
  cases b
  · have h1 := h (UEdge (Original e.1) (AuxiliaryA e.1 e.2.2)) (by simp [PathEdges])
    have h2 := h (UEdge (AuxiliaryA e.1 e.2.2) (Original e.2.1)) (by simp [PathEdges])
    rw [proper_uedge] at h1 h2
    cases hx : x (Original e.1) <;> cases ha : x (AuxiliaryA e.1 e.2.2) <;>
      cases hy : x (Original e.2.1) <;> simp_all
  · have h1 := h (UEdge (Original e.1) (AuxiliaryA e.1 e.2.2)) (by simp [PathEdges])
    have h2 := h (UEdge (AuxiliaryA e.1 e.2.2) (AuxiliaryP e.1 e.2.2)) (by simp [PathEdges])
    have h3 := h (UEdge (AuxiliaryP e.1 e.2.2) (Original e.2.1)) (by simp [PathEdges])
    rw [proper_uedge] at h1 h2 h3
    cases hx : x (Original e.1) <;> cases ha : x (AuxiliaryA e.1 e.2.2) <;>
      cases hp : x (AuxiliaryP e.1 e.2.2) <;> cases hy : x (Original e.2.1) <;> simp_all

private def Extend {n : ℕ} (x : Fin n → Bool) (v : Fin (7*n)) : Bool :=
  if h : v.val < n then x ⟨v.val,h⟩
  else if h' : (v.val-n)/6 < n then
    if (v.val-n)%2 = 0 then !(x ⟨(v.val-n)/6,h'⟩) else x ⟨(v.val-n)/6,h'⟩
  else false

private lemma extend_original {n : ℕ} (x : Fin n → Bool) (u : Fin n) :
    Extend x (Original u) = x u := by simp [Extend, Original, u.isLt]
private lemma extend_A {n : ℕ} (x : Fin n → Bool) (u : Fin n) (j : Fin 3) :
    Extend x (AuxiliaryA u j) = !(x u) := by
  have hu := u.isLt
  have hj := j.isLt
  have hdiv : (6*u.val+2*j.val)/6 = u.val := by omega
  have hmod : (6*u.val+2*j.val)%2 = 0 := by omega
  have hn : ¬ n+6*u.val+2*j.val < n := by omega
  have hs : n+6*u.val+2*j.val-n = 6*u.val+2*j.val := by omega
  simp [Extend, AuxiliaryA, hn, hs, hdiv, hmod, hu]
private lemma extend_P {n : ℕ} (x : Fin n → Bool) (u : Fin n) (j : Fin 3) :
    Extend x (AuxiliaryP u j) = x u := by
  have hu := u.isLt
  have hj := j.isLt
  have hdiv : (6*u.val+2*j.val+1)/6 = u.val := by omega
  have hmod : (6*u.val+2*j.val+1)%2 = 1 := by omega
  have hn : ¬ n+6*u.val+2*j.val+1 < n := by omega
  have hs : n+6*u.val+2*j.val+1-n = 6*u.val+2*j.val+1 := by omega
  simp [Extend, AuxiliaryP, hn, hs, hdiv, hmod, hu]

private lemma extend_path {n : ℕ} (x : Fin n → Bool) (e : ColoredEdge n) (b : Bool)
    (h : xor (x e.1) (x e.2.1) = b) :
    ∀ a ∈ PathEdges e b, Extend x a.1 ≠ Extend x a.2 := by
  intro a ha
  cases b <;> simp only [PathEdges, Bool.false_eq_true, ↓reduceIte,
    mem_insert, mem_singleton] at ha
  · rcases ha with rfl | rfl <;> rw [proper_uedge]
    · simp [extend_original, extend_A]
    · rw [extend_A, extend_original]
      cases hx : x e.1 <;> cases hy : x e.2.1 <;> simp_all
  · rcases ha with rfl | rfl | rfl <;> rw [proper_uedge]
    · simp [extend_original, extend_A]
    · simp [extend_A, extend_P]
    · rw [extend_P, extend_original]
      cases hx : x e.1 <;> cases hy : x e.2.1 <;> simp_all

private lemma gadget_bipartite {n : ℕ} (F : Finset (ColoredEdge n))
    (b : ColoredEdge n → Bool) : Bipartite (Gadget F b) ↔ Balanced F b := by
  constructor
  · rintro ⟨x,hx⟩
    refine ⟨fun u => x (Original u), fun e he => path_parity x e (b e) ?_⟩
    intro a ha
    exact hx a (mem_biUnion.mpr ⟨e,he,ha⟩)
  · rintro ⟨x,hx⟩
    refine ⟨Extend x, ?_⟩
    intro a ha
    obtain ⟨e,he,ha⟩ := mem_biUnion.mp ha
    exact extend_path x e (b e) (hx e he) a ha

private def Owner {n : ℕ} (v : Fin (7*n)) : ℕ × ℕ :=
  ((v.val-n)/6, ((v.val-n)%6)/2)

private lemma owner_A {n : ℕ} (u : Fin n) (j : Fin 3) :
    Owner (AuxiliaryA u j) = (u.val,j.val) := by
  have hj := j.isLt
  simp only [Owner, AuxiliaryA]
  congr 1 <;> omega
private lemma owner_P {n : ℕ} (u : Fin n) (j : Fin 3) :
    Owner (AuxiliaryP u j) = (u.val,j.val) := by
  have hj := j.isLt
  simp only [Owner, AuxiliaryP]
  congr 1 <;> omega

private lemma path_normal {n : ℕ} (e : ColoredEdge n) (b : Bool) :
    PathEdges e b = if b then
      {(Original e.1, AuxiliaryA e.1 e.2.2),
       (AuxiliaryA e.1 e.2.2, AuxiliaryP e.1 e.2.2),
       (Original e.2.1, AuxiliaryP e.1 e.2.2)}
    else {(Original e.1, AuxiliaryA e.1 e.2.2),
       (Original e.2.1, AuxiliaryA e.1 e.2.2)} := by
  have h1 := le_of_lt (original_lt_A e.1 e.1 e.2.2)
  have h2 := le_of_lt (original_lt_A e.2.1 e.1 e.2.2)
  have h3 := le_of_lt (original_lt_P e.2.1 e.1 e.2.2)
  have h4 := le_of_lt (A_lt_P e.1 e.2.2)
  simp [PathEdges, UEdge, min_eq_left h1, max_eq_right h1,
    min_eq_right h2, max_eq_left h2, min_eq_right h3, max_eq_left h3,
    min_eq_left h4, max_eq_right h4]

private lemma path_owner {n : ℕ} (e : ColoredEdge n) (b : Bool) (a : Edge (7*n))
    (ha : a ∈ PathEdges e b) : Owner a.2 = (e.1.val,e.2.2.val) := by
  rw [path_normal] at ha
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, mem_insert, mem_singleton] at ha
  · rcases ha with rfl | rfl <;> exact owner_A _ _
  · rcases ha with rfl | rfl | rfl
    · exact owner_A _ _
    · exact owner_P _ _
    · exact owner_P _ _

private lemma path_disjoint {n : ℕ} (F : Finset (ColoredEdge n)) (hF : Consistent F)
    (b : ColoredEdge n → Bool) : (F : Set (ColoredEdge n)).PairwiseDisjoint (fun e => PathEdges e (b e)) := by
  intro e he f hf hne
  apply Finset.disjoint_left.mpr
  intro a hae haf
  have hh := (path_owner e (b e) a hae).symm.trans (path_owner f (b f) a haf)
  have hu : e.1 = f.1 := Fin.ext (congrArg Prod.fst hh)
  have hj : e.2.2 = f.2.2 := Fin.ext (congrArg Prod.snd hh)
  exact hne (hF.2 e he f hf hj ⟨e.1,Or.inl rfl,Or.inl hu.symm⟩)


private lemma original_inj {n : ℕ} {u v : Fin n} (h : Original u = Original v) : u = v := by
  apply Fin.ext
  exact congrArg (fun a : Fin (7*n) => a.val) h

private def FirstNbr {n : ℕ} (e : ColoredEdge n) (u : Fin n) (b : Bool) : Fin (7*n) :=
  if e.1 = u then AuxiliaryA e.1 e.2.2
  else if b then AuxiliaryP e.1 e.2.2 else AuxiliaryA e.1 e.2.2

private lemma original_neighbor_path {n : ℕ} (e : ColoredEdge n) (b : Bool)
    (he : e.1 < e.2.1) (u : Fin n) (v : Fin (7*n))
    (h : (Original u,v) ∈ PathEdges e b ∨ (v,Original u) ∈ PathEdges e b) :
    Incident e u ∧ v = FirstNbr e u b := by
  have hA : ∀ a j, Original u ≠ AuxiliaryA a j := fun a j => ne_of_lt (original_lt_A u a j)
  have hP : ∀ a j, Original u ≠ AuxiliaryP a j := fun a j => ne_of_lt (original_lt_P u a j)
  rw [path_normal] at h
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, mem_insert, mem_singleton,
    Prod.mk.injEq] at h
  · rcases h with (⟨h,rfl⟩ | ⟨h,rfl⟩) | (⟨_,h⟩ | ⟨_,h⟩)
    · have hu := original_inj h
      subst u
      simp [Incident, FirstNbr]
    · have hu := original_inj h
      subst u
      simp [Incident, FirstNbr, ne_of_lt he]
    · exact (hA _ _ h).elim
    · exact (hA _ _ h).elim
  · rcases h with (⟨h,rfl⟩ | ⟨h,_⟩ | ⟨h,rfl⟩) | (⟨_,h⟩ | ⟨_,h⟩ | ⟨_,h⟩)
    · have hu := original_inj h
      subst u
      simp [Incident, FirstNbr]
    · exact (hA _ _ h).elim
    · have hu := original_inj h
      subst u
      simp [Incident, FirstNbr, ne_of_lt he]
    · exact (hA _ _ h).elim
    · exact (hP _ _ h).elim
    · exact (hP _ _ h).elim


private lemma auxiliary_owner {n : ℕ} (e : ColoredEdge n) (b : Bool)
    (v z : Fin (7*n)) (hv : ∀ u : Fin n, v ≠ Original u)
    (hz : (v,z) ∈ PathEdges e b ∨ (z,v) ∈ PathEdges e b) :
    Owner v = (e.1.val,e.2.2.val) := by
  rw [path_normal] at hz
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, mem_insert, mem_singleton,
    Prod.mk.injEq] at hz
  · rcases hz with (⟨h,_⟩ | ⟨h,_⟩) | (⟨_,rfl⟩ | ⟨_,rfl⟩)
    · exact (hv _ h).elim
    · exact (hv _ h).elim
    · exact owner_A _ _
    · exact owner_A _ _
  · rcases hz with (⟨h,_⟩ | ⟨rfl,_⟩ | ⟨h,_⟩) | (⟨_,rfl⟩ | ⟨_,rfl⟩ | ⟨_,rfl⟩)
    · exact (hv _ h).elim
    · exact owner_A _ _
    · exact (hv _ h).elim
    · exact owner_A _ _
    · exact owner_P _ _
    · exact owner_P _ _

private lemma neighbor_witness {n : ℕ} (F : Finset (ColoredEdge n))
    (b : ColoredEdge n → Bool) (v z : Fin (7*n)) (hz : z ∈ Neighbors (Gadget F b) v) :
    ∃ e ∈ F, (v,z) ∈ PathEdges e (b e) ∨ (z,v) ∈ PathEdges e (b e) := by
  rcases (mem_filter.mp hz).2 with hz | hz
  · obtain ⟨e,he,hz⟩ := mem_biUnion.mp hz
    exact ⟨e,he,Or.inl hz⟩
  · obtain ⟨e,he,hz⟩ := mem_biUnion.mp hz
    exact ⟨e,he,Or.inr hz⟩


private def BaseVertex {n : ℕ} (v : Fin (7*n)) : Fin n :=
  if h : v.val < n then ⟨v.val,h⟩ else ⟨(v.val-n)/6, by have hv := v.isLt; omega⟩

private lemma base_original {n : ℕ} (u : Fin n) : BaseVertex (Original u) = u := by
  simp [BaseVertex, Original, u.isLt]

private lemma base_incident {n : ℕ} (e : ColoredEdge n) (b : Bool) (he : e.1 < e.2.1)
    (v z : Fin (7*n))
    (hz : (v,z) ∈ PathEdges e b ∨ (z,v) ∈ PathEdges e b) :
    Incident e (BaseVertex v) := by
  by_cases ho : ∃ u : Fin n, v = Original u
  · obtain ⟨u,rfl⟩ := ho
    rw [base_original]
    exact (original_neighbor_path e b he u z hz).1
  · have hv : ∀ u : Fin n, v ≠ Original u := by simpa only [not_exists] using ho
    have hown := congrArg Prod.fst (auxiliary_owner e b v z hv hz)
    have hn : ¬ v.val < n := by
      intro hn
      apply hv ⟨v.val,hn⟩
      apply Fin.ext
      rfl
    have hb : BaseVertex v = e.1 := by
      apply Fin.ext
      simpa [BaseVertex,hn,Owner] using hown
    exact Or.inl hb.symm

private def Other {n : ℕ} (e : ColoredEdge n) (u : Fin n) : Fin n :=
  if e.1 = u then e.2.1 else e.1

private lemma reconstruct {n : ℕ} (e : ColoredEdge n) (u : Fin n)
    (he : e.1 < e.2.1) (hu : Incident e u) :
    e = (min u (Other e u),max u (Other e u),e.2.2) := by
  rcases hu with h | h
  · subst u
    simp [Other,min_eq_left (le_of_lt he),max_eq_right (le_of_lt he)]
  · subst u
    simp [Other,ne_of_lt he,min_eq_right (le_of_lt he),max_eq_left (le_of_lt he)]

private lemma response_some {n : ℕ} (F : Finset (ColoredEdge n)) (hF : Consistent F)
    (b : ColoredEdge n → Bool) (u v : Fin n) (j : Fin 3) (s : Bool) :
    SignedResponse F b (u,j) = some (v,s) ↔
      ∃ e ∈ F, e.2.2 = j ∧ Incident e u ∧ Other e u = v ∧ b e = s := by
  unfold SignedResponse
  split_ifs with h
  · have hc := h.choose_spec
    constructor
    · intro hs
      simp only [Option.some.injEq, Prod.mk.injEq] at hs
      exact ⟨h.choose,hc.1,hc.2.1,hc.2.2,hs.1,hs.2⟩
    · rintro ⟨e,he,hj,hu,hv,hb⟩
      have hh : h.choose = e := hF.2 h.choose hc.1 e he (hc.2.1.trans hj.symm)
        ⟨u,hc.2.2,hu⟩
      simp only [hh, Option.some.injEq, Prod.mk.injEq]
      exact ⟨hv,hb⟩
  · constructor
    · simp
    · rintro ⟨e,he,hj,hu,_,_⟩
      exact (h ⟨e,he,hj,hu⟩).elim

private lemma same_response_edge {n : ℕ} (F F' : Finset (ColoredEdge n))
    (hF : Consistent F) (hF' : Consistent F') (b b' : ColoredEdge n → Bool)
    (u : Fin n) (h : ∀ j, SignedResponse F b (u,j) = SignedResponse F' b' (u,j))
    (e : ColoredEdge n) (he : e ∈ F) (hu : Incident e u) : e ∈ F' ∧ b e = b' e := by
  have hr : SignedResponse F b (u,e.2.2) = some (Other e u,b e) :=
    (response_some F hF b u (Other e u) e.2.2 (b e)).mpr ⟨e,he,rfl,hu,rfl,rfl⟩
  rw [h] at hr
  obtain ⟨f,hf,hj,hfu,hfo,hfb⟩ := (response_some F' hF' b' u _ _ _).mp hr
  have hef : e = f := by
    calc e = (min u (Other e u),max u (Other e u),e.2.2) := reconstruct e u (hF.1 e he) hu
         _ = (min u (Other f u),max u (Other f u),f.2.2) := by rw [hfo,hj]
         _ = f := (reconstruct f u (hF'.1 f hf) hfu).symm
  subst f
  exact ⟨hf,hfb.symm⟩

private lemma same_responses_neighbors {n : ℕ} (F F' : Finset (ColoredEdge n))
    (hF : Consistent F) (hF' : Consistent F') (b b' : ColoredEdge n → Bool)
    (v : Fin (7*n)) (h : ∀ j, SignedResponse F b (BaseVertex v,j) =
      SignedResponse F' b' (BaseVertex v,j)) :
    Neighbors (Gadget F b) v = Neighbors (Gadget F' b') v := by
  have hsub : ∀ (F F' : Finset (ColoredEdge n)) (b b' : ColoredEdge n → Bool),
      Consistent F → Consistent F' →
      (∀ j, SignedResponse F b (BaseVertex v,j) = SignedResponse F' b' (BaseVertex v,j)) →
      Neighbors (Gadget F b) v ⊆ Neighbors (Gadget F' b') v := by
    intro F F' b b' hF hF' h z hz
    obtain ⟨e,he,hepath⟩ := neighbor_witness F b v z hz
    have hinc := base_incident e (b e) (hF.1 e he) v z hepath
    obtain ⟨he',hb⟩ := same_response_edge F F' hF hF' b b' (BaseVertex v) h e he hinc
    rw [hb] at hepath
    apply mem_filter.mpr
    refine ⟨mem_univ _,?_⟩
    rcases hepath with hp | hp
    · exact Or.inl (mem_biUnion.mpr ⟨e,he',hp⟩)
    · exact Or.inr (mem_biUnion.mpr ⟨e,he',hp⟩)
  exact subset_antisymm (hsub F F' b b' hF hF' h) (hsub F' F b' b hF' hF fun j => (h j).symm)

private def QueryAt {n : ℕ} (l : Address (7*n) 3) (j : Fin 3) : Address n 3 :=
  match l.1 with
  | none => (none,j)
  | some v => (some (BaseVertex v),j)

private def LocalValue {n kS kT : ℕ} (ES : Encoding (Fin n × Bool) kS)
    (ET : Encoding (Fin (7*n)) kT) (l : Address (7*n) 3) (c : Fin 3 → Bits kS) : Bits kT :=
  if h : ∃ P : Finset (ColoredEdge n) × (ColoredEdge n → Bool), Consistent P.1 ∧
      ∀ j, ES.code (LiftOracle (SignedResponse P.1 P.2) (QueryAt l j)) = c j then
    ET.code (LiftOracle (PackedOracle (Gadget h.choose.1 h.choose.2)) l)
  else 0

private lemma localValue_correct {n kS kT : ℕ} (ES : Encoding (Fin n × Bool) kS)
    (ET : Encoding (Fin (7*n)) kT) (F : Finset (ColoredEdge n)) (hF : Consistent F)
    (b : ColoredEdge n → Bool) (l : Address (7*n) 3) :
    LocalValue ES ET l (fun j => ES.code (LiftOracle (SignedResponse F b) (QueryAt l j))) =
      ET.code (LiftOracle (PackedOracle (Gadget F b)) l) := by
  unfold LocalValue
  split_ifs with h
  · have hG := h.choose_spec.1
    have hc := h.choose_spec.2
    rcases l with ⟨v,i⟩
    cases v with
    | none => rfl
    | some v =>
      have hn : Neighbors (Gadget h.choose.1 h.choose.2) v = Neighbors (Gadget F b) v := by
        apply same_responses_neighbors h.choose.1 F hG hF h.choose.2 b v
        intro j
        exact ES.injective (hc j)
      change ET.code (PackedOracle (Gadget h.choose.1 h.choose.2) (v,i)) =
        ET.code (PackedOracle (Gadget F b) (v,i))
      simp only [PackedOracle,hn]
  · exact (h ⟨(F,b),hF,fun _ => rfl⟩).elim

private lemma coherent_six : CoherentSimulation 6 := by
  intro n kS kT ES ET
  obtain ⟨w,gates,embed,hinj,hcount,heffect⟩ :=
    local_oracle_simulation n kS kT QueryAt (LocalValue ES ET)
  refine ⟨w,gates,embed,hinj,hcount.le,?_⟩
  intro F hF b ψ
  have hh : (fun l => LocalValue ES ET l
      (fun j => (ES.code ∘ LiftOracle (SignedResponse F b)) (QueryAt l j))) =
      ET.code ∘ LiftOracle (PackedOracle (Gadget F b)) := by
    funext l
    exact localValue_correct ES ET F hF b l
  simpa only [hh] using heffect (ES.code ∘ LiftOracle (SignedResponse F b)) ψ

end
end QuantumBipartiteTesting.Bipartiteness


open QuantumBipartiteTesting.Bipartiteness

theorem solution : CoherentSimulation 6 := coherent_six
