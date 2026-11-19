-- Prove2me | solution 1 for QuantumBipartiteTesting.Bipartiteness.local_oracle_algorithm_compilation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T16:35:36.797496+00:00
-- url     : https://prove2.me/submissions/c28c2aaf-3bb7-4044-a4a8-ef61d044ff0e

import Definitions.Def_QuantumBipartiteTesting_Bipartiteness_Reduction
import Mathlib.LinearAlgebra.Matrix.Reindex

namespace QuantumBipartiteTesting.Bipartiteness.CompilerProof
noncomputable section
open Finset
attribute [local instance] Classical.propDecidable Classical.decEq
set_option maxHeartbeats 1000000
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency.types false

private abbrev Gate (S : Type*) [Fintype S] [DecidableEq S] := Sum (Matrix.unitaryGroup S ℂ) Unit
private def GatesCount {S : Type*} [Fintype S] [DecidableEq S] (gs : List (Gate S)) : ℕ :=
  gs.countP (fun g => g.isRight)

private def GatesMatrix {S : Type*} [Fintype S] [DecidableEq S] (Q : Matrix S S ℂ) : List (Gate S) → Matrix S S ℂ
  | [] => 1
  | Sum.inl U :: gs => GatesMatrix Q gs * U.val
  | Sum.inr _ :: gs => GatesMatrix Q gs * Q

private def UnitsMatrix {S : Type*} [Fintype S] [DecidableEq S] (Q : Matrix S S ℂ) :
    List (Matrix.unitaryGroup S ℂ) → Matrix S S ℂ
  | [] => 1
  | [U] => U.val
  | U :: V :: us => UnitsMatrix Q (V::us)*Q*U.val

private def CompileUnits {S : Type*} [Fintype S] [DecidableEq S] : List (Gate S) → List (Matrix.unitaryGroup S ℂ)
  | [] => [1]
  | Sum.inl U :: gs => ((CompileUnits gs).headD 1*U)::(CompileUnits gs).tail
  | Sum.inr _ :: gs => 1::CompileUnits gs

private lemma compile_nonempty {S : Type*} [Fintype S] [DecidableEq S] (gs : List (Gate S)) :
    CompileUnits gs ≠ [] := by cases gs with | nil => simp [CompileUnits] | cons g gs => cases g <;> simp [CompileUnits]

private lemma compile_length {S : Type*} [Fintype S] [DecidableEq S] (gs : List (Gate S)) :
    (CompileUnits gs).length = GatesCount gs+1 := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    dsimp only [GatesCount] at ih
    cases g <;> simp [CompileUnits,GatesCount] <;> omega

private lemma units_head_mul {S : Type*} [Fintype S] [DecidableEq S] (Q : Matrix S S ℂ)
    (us : List (Matrix.unitaryGroup S ℂ)) (hu : us ≠ []) (U : Matrix.unitaryGroup S ℂ) :
    UnitsMatrix Q ((us.headD 1*U)::us.tail) = UnitsMatrix Q us*U.val := by
  cases us with
  | nil => contradiction
  | cons A rest =>
    cases rest with
    | nil => simp [UnitsMatrix]
    | cons B rest => simp [UnitsMatrix,Matrix.mul_assoc]

private lemma compile_matrix {S : Type*} [Fintype S] [DecidableEq S] (Q : Matrix S S ℂ)
    (gs : List (Gate S)) : UnitsMatrix Q (CompileUnits gs) = GatesMatrix Q gs := by
  induction gs with
  | nil => simp [CompileUnits,UnitsMatrix,GatesMatrix]
  | cons g gs ih =>
    cases g with
    | inl U => rw [CompileUnits,units_head_mul Q _ (compile_nonempty gs),ih]; rfl
    | inr u =>
      have hn := compile_nonempty gs
      cases hu : CompileUnits gs with
      | nil => contradiction
      | cons A rest => simpa [CompileUnits,hu,UnitsMatrix,GatesMatrix] using congrArg (fun M => M*Q) ih

private lemma units_append {S : Type*} [Fintype S] [DecidableEq S] (Q : Matrix S S ℂ)
    (us : List (Matrix.unitaryGroup S ℂ)) (hu : us ≠ []) (U : Matrix.unitaryGroup S ℂ) :
    UnitsMatrix Q (us++[U]) = U.val*Q*UnitsMatrix Q us := by
  induction us with
  | nil => contradiction
  | cons A rest ih =>
    cases rest with
    | nil => simp [UnitsMatrix]
    | cons B rest =>
      simp only [List.cons_append,UnitsMatrix]
      have hh := ih (by simp)
      simp only [List.cons_append] at hh
      rw [hh]
      simp only [Matrix.mul_assoc]

private lemma act_mul {S : Type*} [Fintype S] (M N : Matrix S S ℂ) (ψ : EuclideanSpace ℂ S) :
    QAlgorithms.act M (QAlgorithms.act N ψ) = QAlgorithms.act (M*N) ψ := by
  ext i
  exact congrFun (Matrix.mulVec_mulVec (fun x => ψ x) M N) i

private def Truncate {I B W : Type*} [Fintype I] [Fintype B] [Fintype W]
    [DecidableEq I] [DecidableEq B] [DecidableEq W] {q : ℕ}
    (A : QAlgorithms.QueryAlg I B W (q+1)) : QAlgorithms.QueryAlg I B W q :=
  ⟨A.start,A.start_unit,fun i => A.U i.castSucc⟩

private lemma truncate_state {I B W : Type*} [Fintype I] [Fintype B] [Fintype W]
    [DecidableEq I] [DecidableEq B] [DecidableEq W] {q : ℕ}
    (A : QAlgorithms.QueryAlg I B W (q+1)) (O : Matrix (I×B) (I×B) ℂ) :
    ∀ i : Fin (q+1), A.stateAt O i.castSucc = (Truncate A).stateAt O i := by
  apply Fin.induction
  · rfl
  · intro i ih
    change QAlgorithms.act (A.U i.succ.castSucc : Matrix _ _ ℂ)
      (QAlgorithms.act (Matrix.kronecker O (1:Matrix W W ℂ)) (A.stateAt O i.castSucc.castSucc)) =
      QAlgorithms.act (A.U i.succ.castSucc : Matrix _ _ ℂ)
      (QAlgorithms.act (Matrix.kronecker O (1:Matrix W W ℂ)) ((Truncate A).stateAt O i.castSucc))
    rw [ih]

private lemma algorithm_matrix {I B W : Type*} [Fintype I] [Fintype B] [Fintype W]
    [DecidableEq I] [DecidableEq B] [DecidableEq W] (q : ℕ)
    (A : QAlgorithms.QueryAlg I B W q) (O : Matrix (I×B) (I×B) ℂ) :
    A.finalState O = QAlgorithms.act
      (UnitsMatrix (Matrix.kronecker O (1:Matrix W W ℂ)) (List.ofFn A.U)) A.start := by
  induction q with
  | zero =>
    change QAlgorithms.act (A.U 0 : Matrix _ _ ℂ) A.start = _
    simp [List.ofFn_succ,UnitsMatrix]
  | succ q ih =>
    have hprev := ih (Truncate A)
    have hlast : A.finalState O = QAlgorithms.act (A.U (Fin.last (q+1)) : Matrix _ _ ℂ)
        (QAlgorithms.act (Matrix.kronecker O (1:Matrix W W ℂ)) ((Truncate A).finalState O)) := by
      change QAlgorithms.act (A.U (Fin.last (q+1)) : Matrix _ _ ℂ)
        (QAlgorithms.act (Matrix.kronecker O (1:Matrix W W ℂ)) (A.stateAt O (Fin.last q).castSucc)) = _
      rw [truncate_state]
      rfl
    rw [hlast,hprev]
    conv_rhs => rw [List.ofFn_succ',List.concat_eq_append,units_append _ _ (by simp)]
    rw [act_mul,act_mul]
    rfl

private def CompileAlgorithm {I B W : Type*} [Fintype I] [Fintype B] [Fintype W]
    [DecidableEq I] [DecidableEq B] [DecidableEq W]
    (gs : List (Gate ((I×B)×W))) (ψ : EuclideanSpace ℂ ((I×B)×W)) (hψ : ‖ψ‖ = 1) :
    QAlgorithms.QueryAlg I B W (GatesCount gs) where
  start := ψ
  start_unit := hψ
  U i := (CompileUnits gs)[i.val]'(by rw [compile_length]; exact i.isLt)

private lemma compile_algorithm_matrix {I B W : Type*} [Fintype I] [Fintype B] [Fintype W]
    [DecidableEq I] [DecidableEq B] [DecidableEq W]
    (gs : List (Gate ((I×B)×W))) (ψ : EuclideanSpace ℂ ((I×B)×W)) (hψ : ‖ψ‖ = 1)
    (O : Matrix (I×B) (I×B) ℂ) :
    (CompileAlgorithm gs ψ hψ).finalState O =
      QAlgorithms.act (GatesMatrix (Matrix.kronecker O (1:Matrix W W ℂ)) gs) ψ := by
  rw [algorithm_matrix]
  have hlist : List.ofFn (CompileAlgorithm gs ψ hψ).U = CompileUnits gs := by
    apply List.ext_getElem
    · simp [compile_length]
    · intro i hi hi'
      simp only [List.getElem_ofFn,CompileAlgorithm]
  rw [hlist,compile_matrix]
  rfl

private def ReindexUnitary {S T : Type*} [Fintype S] [Fintype T] [DecidableEq S] [DecidableEq T]
    (e : S ≃ T) (U : Matrix.unitaryGroup S ℂ) : Matrix.unitaryGroup T ℂ :=
  ⟨Matrix.reindex e e U.val,by
    rw [Matrix.mem_unitaryGroup_iff]
    change U.val.submatrix e.symm e.symm * (star U.val).submatrix e.symm e.symm = 1
    rw [Matrix.submatrix_mul_equiv,Matrix.mem_unitaryGroup_iff.mp U.property,Matrix.submatrix_one_equiv]⟩

private lemma reindex_mulVec {S T : Type*} [Fintype S] [Fintype T] [DecidableEq S] [DecidableEq T]
    (e : S ≃ T) (U : Matrix.unitaryGroup S ℂ) (ψ : S → ℂ) :
    (ReindexUnitary e U).val.mulVec (fun t => ψ (e.symm t)) = fun t => (U.val.mulVec ψ) (e.symm t) := by
  simpa only [ReindexUnitary,Matrix.reindex_apply,Function.comp_def,Equiv.symm_symm,Equiv.symm_apply_apply] using
    (Matrix.submatrix_mulVec_equiv U.val (fun t => ψ (e.symm t)) e.symm e.symm)

private lemma sum_injection {S T R : Type*} [Fintype S] [Fintype T] [DecidableEq T] [AddCommMonoid R]
    (e : S → T) (he : Function.Injective e) (f : T → R)
    (hzero : ∀ t, t ∉ (univ.image e) → f t = 0) : (∑ t, f t) = ∑ s, f (e s) := by
  calc
    _ = ∑ t ∈ univ.image e, f t := (sum_subset (subset_univ _) (fun t ht ht' => hzero t ht')).symm
    _ = _ := Finset.sum_image (fun s hs t ht hst => he hst)

private lemma embed_at {S T : Type*} [Fintype S] [DecidableEq T]
    (e : S → T) (he : Function.Injective e) (ψ : S → ℂ) (s : S) : EmbedState e ψ (e s) = ψ s := by
  simp only [EmbedState,he.eq_iff]
  simpa only [mem_univ,if_true] using Finset.sum_ite_eq' univ s ψ

private lemma embed_outside {S T : Type*} [Fintype S] [DecidableEq T]
    (e : S → T) (ψ : S → ℂ) (t : T) (ht : ¬ ∃ s, e s = t) : EmbedState e ψ t = 0 := by
  unfold EmbedState
  apply sum_eq_zero
  intro s hs
  exact if_neg (fun h => ht ⟨s,h⟩)

private lemma embed_norm {S T : Type*} [Fintype S] [Fintype T] [DecidableEq T]
    (e : S → T) (he : Function.Injective e) (ψ : EuclideanSpace ℂ S) :
    ‖WithLp.toLp 2 (EmbedState e (fun s => ψ s))‖ = ‖ψ‖ := by
  have hsum : (∑ t, ‖EmbedState e (fun s => ψ s) t‖^2) = ∑ s, ‖ψ s‖^2 := by
    rw [sum_injection e he _ (by
      intro t ht
      have ho : ¬ ∃ s, e s = t := by intro hh; obtain ⟨s,hs⟩ := hh; exact ht (mem_image.mpr ⟨s,mem_univ _,hs⟩)
      rw [embed_outside e _ t ho]
      simp)]
    simp only [embed_at e he]
  have hsquare : ‖WithLp.toLp 2 (EmbedState e (fun s => ψ s))‖^2 = ‖ψ‖^2 := by
    rw [EuclideanSpace.norm_sq_eq,EuclideanSpace.norm_sq_eq]
    exact hsum
  nlinarith [norm_nonneg (WithLp.toLp 2 (EmbedState e (fun s => ψ s))),norm_nonneg ψ]

private def LiftOutput {S T : Type*} (e : S → T) (out : S → Bool) (t : T) : Bool :=
  if h : ∃ s, e s = t then out h.choose else false

private lemma lift_output_at {S T : Type*} (e : S → T) (he : Function.Injective e) (out : S → Bool) (s : S) :
    LiftOutput e out (e s) = out s := by
  have hex : ∃ s', e s' = e s := ⟨s,rfl⟩
  simp only [LiftOutput,dif_pos hex]
  rw [he hex.choose_spec]

private lemma probability_coords {S : Type*} [Fintype S] [DecidableEq S]
    (ψ : EuclideanSpace ℂ S) (s : S) : QAlgorithms.prob ψ s = ‖ψ s‖^2 := by
  simp only [QAlgorithms.prob,QAlgorithms.ket,EuclideanSpace.inner_single_left,map_one,one_mul]

private lemma embed_probability {S T : Type*} [Fintype S] [Fintype T] [DecidableEq S] [DecidableEq T]
    (e : S → T) (he : Function.Injective e) (ψ : EuclideanSpace ℂ S) (out : S → Bool) :
    QAlgorithms.probEvent (WithLp.toLp 2 (EmbedState e (fun s => ψ s))) (fun t => LiftOutput e out t = true) =
      QAlgorithms.probEvent ψ (fun s => out s = true) := by
  unfold QAlgorithms.probEvent
  rw [Finset.sum_filter,Finset.sum_filter]
  simp only [probability_coords]
  rw [sum_injection e he _ (by
    intro t ht
    have ho : ¬ ∃ s, e s = t := by intro hh; obtain ⟨s,hs⟩ := hh; exact ht (mem_image.mpr ⟨s,mem_univ _,hs⟩)
    simp only [embed_outside e _ t ho,norm_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0),ite_self])]
  apply sum_congr rfl
  intro s hs
  simp only [lift_output_at e he,embed_at e he]

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

private def Realize {S : Type*} [Fintype S] [DecidableEq S] (word : Word S) : List (Gate S) :=
  word.map (Sum.map PermU id)

private lemma realize_matrix {I B W : Type*} [Fintype I] [Fintype B] [Fintype W]
    [DecidableEq I] [DecidableEq B] [DecidableEq W] [AddCommGroup B] (f : I → B)
    (word : Word ((I×B)×W)) :
    GatesMatrix (Matrix.kronecker (QAlgorithms.xorOracle f) (1:Matrix W W ℂ)) (Realize word) =
      (PermU (WordPerm (QueryPerm f) word)).val := by
  induction word with
  | nil =>
    change (1 : Matrix ((I×B)×W) ((I×B)×W) ℂ) = (PermU (Equiv.refl ((I×B)×W))).val
    change (1 : Matrix _ _ ℂ) = ((1 : Equiv.Perm ((I×B)×W))⁻¹).permMatrix ℂ
    simp
  | cons g gs ih =>
    cases g with
    | inl p =>
      change GatesMatrix (Matrix.kronecker (QAlgorithms.xorOracle f) 1) (Realize gs)*PermU p = _
      rw [ih]
      exact permU_mul p (WordPerm (QueryPerm f) gs)
    | inr u =>
      change GatesMatrix (Matrix.kronecker (QAlgorithms.xorOracle f) 1) (Realize gs)*
        Matrix.kronecker (QAlgorithms.xorOracle f) 1 = _
      rw [ih,query_matrix]
      exact permU_mul (QueryPerm (W := W) f) (WordPerm (QueryPerm f) gs)

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

private lemma realized_count {S : Type*} [Fintype S] [DecidableEq S] (word : Word S) :
    GatesCount (Realize word) = word.countP (fun g => g.isRight) := by
  simp only [GatesCount,Realize,List.countP_map]
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


private def OuterEquiv {I L W : Type*} {kS kT : ℕ} :
    WorkBasis I (L×W) kS kT ≃ (((I×Bits kS)×(Fin 3→Bits kS))×((L×Bits kT)×W)) where
  toFun s := ((s.1,s.2.2),((s.2.1.1.1,s.2.1.2),s.2.1.1.2))
  invFun r := (r.1.1,(((r.2.1.1,r.2.2),r.2.1.2),r.1.2))
  left_inv _ := rfl
  right_inv _ := rfl

private def RawEmbed {I L W : Type*} {kS kT : ℕ} (i0 : I) (b : (L×Bits kT)×W) :
    WorkBasis I (L×W) kS kT := Seed i0 ((b.1.1,b.2),b.1.2)

private lemma rawEmbed_injective {I L W : Type*} {kS kT : ℕ} (i0 : I) :
    Function.Injective (RawEmbed (L:=L) (W:=W) (kS:=kS) (kT:=kT) i0) := by
  intro a b h
  have hh := congrArg (fun s => (OuterEquiv s).2) h
  exact hh

private def TensorUnitary {S T : Type*} [Fintype S] [Fintype T] [DecidableEq S] [DecidableEq T]
    (U : Matrix.unitaryGroup T ℂ) : Matrix.unitaryGroup (S×T) ℂ :=
  ⟨Matrix.kronecker (1:Matrix S S ℂ) U.val,Matrix.kronecker_mem_unitary (one_mem _) U.property⟩

private def LiftURaw {I L W : Type*} [Fintype I] [Fintype L] [Fintype W]
    [DecidableEq I] [DecidableEq L] [DecidableEq W] {kS kT : ℕ}
    (U : Matrix.unitaryGroup ((L×Bits kT)×W) ℂ) :
    Matrix.unitaryGroup (WorkBasis I (L×W) kS kT) ℂ :=
  ⟨Matrix.reindex (OuterEquiv (I:=I) (L:=L) (W:=W) (kS:=kS) (kT:=kT)).symm
    OuterEquiv.symm (Matrix.kronecker (1:Matrix ((I×Bits kS)×(Fin 3→Bits kS)) _ ℂ) U.val),by
    rw [Matrix.mem_unitaryGroup_iff]
    change (Matrix.kronecker (1:Matrix ((I×Bits kS)×(Fin 3→Bits kS)) _ ℂ) U.val).submatrix OuterEquiv OuterEquiv *
      (star (Matrix.kronecker (1:Matrix ((I×Bits kS)×(Fin 3→Bits kS)) _ ℂ) U.val)).submatrix OuterEquiv OuterEquiv = 1
    rw [Matrix.submatrix_mul_equiv]
    letI : DecidableEq (((I×Bits kS)×(Fin 3→Bits kS))×((L×Bits kT)×W)) := instDecidableEqProd
    have hM := (Matrix.kronecker_mem_unitary (show (1:Matrix ((I×Bits kS)×(Fin 3→Bits kS)) _ ℂ) ∈ Matrix.unitaryGroup _ ℂ from one_mem _) U.property).2
    change Matrix.kronecker (1:Matrix ((I×Bits kS)×(Fin 3→Bits kS)) _ ℂ) U.val * star (Matrix.kronecker (1:Matrix ((I×Bits kS)×(Fin 3→Bits kS)) _ ℂ) U.val) = 1 at hM
    rw [hM,Matrix.submatrix_one_equiv]⟩

private lemma reindex_matrix_mulVec {S T : Type*} [Fintype S] [Fintype T]
    (e : S≃T) (M : Matrix S S ℂ) (ψ : S→ℂ) :
    (Matrix.reindex e e M).mulVec (fun t => ψ (e.symm t)) = fun t => (M.mulVec ψ) (e.symm t) := by
  simpa only [Matrix.reindex_apply,Function.comp_def,Equiv.symm_symm,Equiv.symm_apply_apply] using
    (Matrix.submatrix_mulVec_equiv M (fun t => ψ (e.symm t)) e.symm e.symm)

private lemma seed_embed_value {S T : Type*} [Fintype T] [DecidableEq S] [DecidableEq T]
    (s0 : S) (ψ : T→ℂ) (s : S) (t : T) :
    EmbedState (fun t => (s0,t)) ψ (s,t) = if s0=s then ψ t else 0 := by
  by_cases h : s0=s
  · subst s
    exact (embed_at (fun t => (s0,t)) (by intro a b h; exact (Prod.mk.inj h).2) ψ t).trans (if_pos rfl).symm
  · simp only [EmbedState,Prod.mk.injEq]
    simp [h]

private lemma tensor_seed {S T : Type*} [Fintype S] [Fintype T] [DecidableEq S] [DecidableEq T]
    (s0 : S) (U : Matrix.unitaryGroup T ℂ) (ψ : T→ℂ) :
    (TensorUnitary (S:=S) U).val.mulVec (EmbedState (fun t => (s0,t)) ψ) =
      EmbedState (fun t => (s0,t)) (U.val.mulVec ψ) := by
  ext ⟨s,t⟩
  simp only [TensorUnitary,Matrix.mulVec, dotProduct,Fintype.sum_prod_type,
    Matrix.kronecker_apply,Matrix.one_apply,seed_embed_value]
  by_cases h : s0=s
  · subst s
    simp
  · simp [h,Ne.symm h]

private lemma embed_transport {S T Z : Type*} [Fintype S] [DecidableEq T] [DecidableEq Z]
    (e : T≃Z) (b : S→T) (ψ : S→ℂ) :
    EmbedState (fun s => e (b s)) ψ = fun z => EmbedState b ψ (e.symm z) := by
  ext z
  simp only [EmbedState]
  apply sum_congr rfl
  intro s hs
  rw [e.apply_eq_iff_eq_symm_apply]

private lemma lift_raw_action {I L W : Type*} [Fintype I] [Fintype L] [Fintype W]
    [DecidableEq I] [DecidableEq L] [DecidableEq W] {kS kT : ℕ}
    (i0 : I) (U : Matrix.unitaryGroup ((L×Bits kT)×W) ℂ) (ψ : ((L×Bits kT)×W)→ℂ) :
    (LiftURaw (I:=I) (kS:=kS) U).val.mulVec (EmbedState (RawEmbed i0) ψ) =
      EmbedState (RawEmbed i0) (U.val.mulVec ψ) := by
  have hb : RawEmbed (I:=I) (L:=L) (W:=W) (kS:=kS) (kT:=kT) i0 = fun b => OuterEquiv.symm (((i0,0),0),b) := rfl
  rw [hb,embed_transport]
  change (Matrix.reindex (OuterEquiv (I:=I) (L:=L) (W:=W) (kS:=kS) (kT:=kT)).symm OuterEquiv.symm
    (TensorUnitary (S:=((I×Bits kS)×(Fin 3→Bits kS))) U).val).mulVec _ = _
  rw [reindex_matrix_mulVec,tensor_seed]
  exact (embed_transport OuterEquiv.symm _ _).symm

section FiniteCompiler
variable {I L W : Type*} [Fintype I] [Fintype L] [Fintype W]
  [DecidableEq I] [DecidableEq L] [DecidableEq W] {kS kT : ℕ}

private abbrev MemorySize (L W : Type*) [Fintype L] [Fintype W] (kS kT : ℕ) :=
  Fintype.card (Memory (L×W) kS kT)

private def BasisEquiv : WorkBasis I (L×W) kS kT ≃ ((I×Bits kS)×Fin (MemorySize L W kS kT)) :=
  Equiv.prodCongr (Equiv.refl _) (Fintype.equivFin _)

private def BasisEmbed (i0 : I) : ((L×Bits kT)×W) → ((I×Bits kS)×Fin (MemorySize L W kS kT)) :=
  fun b => BasisEquiv (RawEmbed i0 b)

private lemma basisEmbed_injective (i0 : I) : Function.Injective (BasisEmbed (L:=L) (W:=W) (kS:=kS) (kT:=kT) i0) :=
  BasisEquiv.injective.comp (rawEmbed_injective i0)

private def LiftU (U : Matrix.unitaryGroup ((L×Bits kT)×W) ℂ) :
    Matrix.unitaryGroup ((I×Bits kS)×Fin (MemorySize L W kS kT)) ℂ :=
  ReindexUnitary (BasisEquiv (I:=I) (L:=L) (W:=W) (kS:=kS) (kT:=kT)) (LiftURaw U)

private lemma lift_action (i0 : I) (U : Matrix.unitaryGroup ((L×Bits kT)×W) ℂ) (ψ : ((L×Bits kT)×W)→ℂ) :
    (LiftU (I:=I) (kS:=kS) U).val.mulVec (EmbedState (BasisEmbed i0) ψ) =
      EmbedState (BasisEmbed i0) (U.val.mulVec ψ) := by
  change (ReindexUnitary (BasisEquiv (I:=I) (L:=L) (W:=W) (kS:=kS) (kT:=kT)) (LiftURaw U)).val.mulVec
    (EmbedState (fun b => BasisEquiv (RawEmbed i0 b)) ψ) =
    EmbedState (fun b => BasisEquiv (RawEmbed i0 b)) (U.val.mulVec ψ)
  rw [embed_transport,reindex_mulVec,lift_raw_action]
  exact (embed_transport BasisEquiv _ _).symm

private def SimGates (i0 : I) (a : L→Fin 3→I) (g : L→(Fin 3→Bits kS)→Bits kT) :
    List (Gate ((I×Bits kS)×Fin (MemorySize L W kS kT))) :=
  Realize (TransportWord BasisEquiv (SimulationWord i0 (fun t : L×W => a t.1) (fun t : L×W => g t.1)))

private lemma sim_count (i0 : I) (a : L→Fin 3→I) (g : L→(Fin 3→Bits kS)→Bits kT) :
    GatesCount (SimGates (W:=W) i0 a g) = 6 := by
  rw [SimGates,realized_count,transport_count,simulation_count]

private lemma sim_action (i0 : I) (a : L→Fin 3→I) (g : L→(Fin 3→Bits kS)→Bits kT)
    (f : I→Bits kS) (ψ : ((L×Bits kT)×W)→ℂ) :
    (GatesMatrix (Matrix.kronecker (QAlgorithms.xorOracle f) (1:Matrix _ _ ℂ))
      (SimGates i0 a g)).mulVec (EmbedState (BasisEmbed i0) ψ) =
      EmbedState (BasisEmbed i0) ((Matrix.kronecker
        (QAlgorithms.xorOracle (fun l => g l (fun j => f (a l j)))) (1:Matrix W W ℂ)).mulVec ψ) := by
  rw [SimGates,realize_matrix,transport_wordPerm BasisEquiv _ _
    (memory_query_conjugate (Fintype.equivFin _) f),perm_embed,query_matrix,embed_perm]
  congr 1
  funext b
  change Conjugate BasisEquiv (WordPerm (QueryPerm f)
    (SimulationWord i0 (fun t : L×W => a t.1) (fun t : L×W => g t.1)))
    (BasisEquiv (RawEmbed i0 b)) = BasisEquiv (RawEmbed i0 (QueryPerm _ b))
  rw [conjugate_apply]
  change BasisEquiv (WordPerm (QueryPerm f) (SimulationWord i0 _ _)
    (Seed i0 ((b.1.1,b.2),b.1.2))) = _
  rw [simulationWord_seed]
  rfl

private def EmbedV (i0 : I) (ψ : EuclideanSpace ℂ ((L×Bits kT)×W)) :
    EuclideanSpace ℂ ((I×Bits kS)×Fin (MemorySize L W kS kT)) :=
  WithLp.toLp 2 (EmbedState (BasisEmbed i0) (fun b => ψ b))

private lemma lift_act (i0 : I) (U : Matrix.unitaryGroup ((L×Bits kT)×W) ℂ)
    (ψ : EuclideanSpace ℂ ((L×Bits kT)×W)) :
    QAlgorithms.act (LiftU (I:=I) (kS:=kS) U).val (EmbedV i0 ψ) =
      EmbedV i0 (QAlgorithms.act U.val ψ) := by
  ext b
  exact congrFun (lift_action i0 U (fun b => ψ b)) b

private lemma sim_act (i0 : I) (a : L→Fin 3→I) (g : L→(Fin 3→Bits kS)→Bits kT)
    (f : I→Bits kS) (ψ : EuclideanSpace ℂ ((L×Bits kT)×W)) :
    QAlgorithms.act (GatesMatrix (Matrix.kronecker (QAlgorithms.xorOracle f) (1:Matrix _ _ ℂ))
      (SimGates i0 a g)) (EmbedV i0 ψ) =
      EmbedV i0 (QAlgorithms.act (Matrix.kronecker
        (QAlgorithms.xorOracle (fun l => g l (fun j => f (a l j)))) (1:Matrix W W ℂ)) ψ) := by
  ext b
  exact congrFun (sim_action i0 a g f (fun b => ψ b)) b

private lemma gates_append {S : Type*} [Fintype S] [DecidableEq S] (Q : Matrix S S ℂ)
    (as bs : List (Gate S)) : GatesMatrix Q (as++bs) = GatesMatrix Q bs * GatesMatrix Q as := by
  induction as with
  | nil => simp [GatesMatrix]
  | cons a as ih => cases a <;> simp [GatesMatrix,ih,Matrix.mul_assoc]

private def AlgorithmGates (i0 : I) (a : L→Fin 3→I) (g : L→(Fin 3→Bits kS)→Bits kT) :
    (q : ℕ) → QAlgorithms.QueryAlg L (Bits kT) W q →
      List (Gate ((I×Bits kS)×Fin (MemorySize L W kS kT)))
  | 0,A => [Sum.inl (LiftU (A.U 0))]
  | q+1,A => AlgorithmGates i0 a g q (Truncate A) ++ SimGates i0 a g ++
      [Sum.inl (LiftU (A.U (Fin.last (q+1))))]

private lemma algorithm_count (i0 : I) (a : L→Fin 3→I) (g : L→(Fin 3→Bits kS)→Bits kT)
    (q : ℕ) (A : QAlgorithms.QueryAlg L (Bits kT) W q) :
    GatesCount (AlgorithmGates i0 a g q A) = 6*q := by
  induction q with
  | zero => rfl
  | succ q ih =>
    change GatesCount (_++_++_) = _
    simp only [GatesCount,List.countP_append]
    have hh := sim_count (W:=W) i0 a g
    have hi := ih (Truncate A)
    dsimp only [GatesCount] at hh hi
    simp only [List.countP_cons,List.countP_nil,Sum.isRight_inl,Bool.false_eq_true,↓reduceIte]
    omega

private lemma final_succ {J B Z : Type*} [Fintype J] [Fintype B] [Fintype Z]
    [DecidableEq J] [DecidableEq B] [DecidableEq Z] {q : ℕ}
    (A : QAlgorithms.QueryAlg J B Z (q+1)) (O : Matrix (J×B) (J×B) ℂ) :
    A.finalState O = QAlgorithms.act (A.U (Fin.last (q+1))).val
      (QAlgorithms.act (Matrix.kronecker O (1:Matrix Z Z ℂ)) ((Truncate A).finalState O)) := by
  change QAlgorithms.act (A.U (Fin.last (q+1))).val
    (QAlgorithms.act (Matrix.kronecker O (1:Matrix Z Z ℂ)) (A.stateAt O (Fin.last q).castSucc)) = _
  rw [truncate_state]
  rfl

private lemma algorithm_action (i0 : I) (a : L→Fin 3→I) (g : L→(Fin 3→Bits kS)→Bits kT)
    (f : I→Bits kS) (q : ℕ) (A : QAlgorithms.QueryAlg L (Bits kT) W q) :
    QAlgorithms.act (GatesMatrix (Matrix.kronecker (QAlgorithms.xorOracle f) (1:Matrix _ _ ℂ))
      (AlgorithmGates i0 a g q A)) (EmbedV i0 A.start) =
      EmbedV i0 (A.finalState (QAlgorithms.xorOracle (fun l => g l (fun j => f (a l j))))) := by
  induction q with
  | zero =>
    change QAlgorithms.act (1*(LiftU (A.U 0)).val) (EmbedV i0 A.start) = _
    rw [Matrix.one_mul,lift_act]
    rfl
  | succ q ih =>
    rw [AlgorithmGates,gates_append,gates_append]
    simp only [GatesMatrix,Matrix.one_mul]
    rw [← act_mul,← act_mul]
    rw [show A.start = (Truncate A).start from rfl,ih (Truncate A),sim_act,lift_act]
    rw [final_succ]

private lemma compiler_correct (kS kT q : ℕ) (i0 : I) (a : L→Fin 3→I)
    (g : L→(Fin 3→Bits kS)→Bits kT) (A : QAlgorithms.QueryAlg L (Bits kT) W q)
    (out : ((L×Bits kT)×W)→Bool) :
    ∃ wS qS : ℕ, ∃ A' : Algorithm I kS wS qS,
    ∃ out' : ((I×Bits kS)×Fin wS)→Bool, qS ≤ 6*q ∧ ∀ f : I→Bits kS,
      A'.outputProb (QAlgorithms.xorOracle f) out' true =
        A.outputProb (QAlgorithms.xorOracle (fun l => g l (fun j => f (a l j)))) out true := by
  let gs := AlgorithmGates (W:=W) i0 a g q A
  have hn : ‖EmbedV (kS:=kS) i0 A.start‖ = 1 :=
    (embed_norm (BasisEmbed i0) (basisEmbed_injective i0) A.start).trans A.start_unit
  refine ⟨MemorySize L W kS kT,GatesCount gs,CompileAlgorithm gs (EmbedV i0 A.start) hn,
    LiftOutput (BasisEmbed i0) out,(algorithm_count i0 a g q A).le,?_⟩
  intro f
  unfold QAlgorithms.QueryAlg.outputProb
  rw [compile_algorithm_matrix]
  change QAlgorithms.probEvent (QAlgorithms.act (GatesMatrix _ (AlgorithmGates i0 a g q A))
    (EmbedV i0 A.start)) _ = _
  rw [algorithm_action]
  exact embed_probability (BasisEmbed i0) (basisEmbed_injective i0) _ out

end FiniteCompiler


end
end QuantumBipartiteTesting.Bipartiteness.CompilerProof

open QuantumBipartiteTesting.Bipartiteness
open QuantumBipartiteTesting.Bipartiteness.CompilerProof

theorem solution {I L : Type} [Fintype I] [Fintype L] [DecidableEq I] [DecidableEq L]
    (kS kT w q : ℕ) (i0 : I) (a : L→Fin 3→I)
    (g : L→(Fin 3→Bits kS)→Bits kT) (A : Algorithm L kT w q)
    (out : ((L×Bits kT)×Fin w)→Bool) :
    ∃ wS qS : ℕ, ∃ A' : Algorithm I kS wS qS,
    ∃ out' : ((I×Bits kS)×Fin wS)→Bool, qS ≤ 6*q ∧ ∀ f : I→Bits kS,
      A'.outputProb (QAlgorithms.xorOracle f) out' true =
        A.outputProb (QAlgorithms.xorOracle (fun l => g l (fun j => f (a l j)))) out true := by
  exact compiler_correct kS kT q i0 a g A out
