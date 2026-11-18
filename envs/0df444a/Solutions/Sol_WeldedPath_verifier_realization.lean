-- Prove2me | solution 1 for WeldedPath.verifier_realization
-- status  : ACCEPTED   (prove)
-- author  : @dmilosch
-- created : 2026-11-17T17:18:04.344011+00:00
-- url     : https://prove2.me/submissions/9abb8739-54f8-47fb-a28c-f377d4531d4f

import Definitions.Def_QAlgorithms_Defs_Query
import Mathlib.LinearAlgebra.Matrix.Permutation
import Definitions.Def_WeldedPath_Supplement_pWt
import Mathlib.Data.List.GetD

set_option autoImplicit false

-- Solutions.QueryAlgAppend
section

namespace QAlgorithms.QueryAlg

variable {ι κ W : Type*} [Fintype ι] [Fintype κ] [Fintype W]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq W] {q : ℕ}

theorem act_mul_eq {Z : Type*} [Fintype Z] (U V : Matrix Z Z ℂ)
    (ψ : EuclideanSpace ℂ Z) : act (U * V) ψ = act U (act V ψ) := by
  simp [act, Matrix.mulVec_mulVec]

noncomputable def postUnitary (A : QueryAlg ι κ W q)
    (V : Matrix.unitaryGroup ((ι × κ) × W) ℂ) : QueryAlg ι κ W q where
  start := A.start
  start_unit := A.start_unit
  U i := if i = Fin.last q then V * A.U i else A.U i

theorem stateAt_postUnitary (A : QueryAlg ι κ W q)
    (V : Matrix.unitaryGroup ((ι × κ) × W) ℂ)
    (O : Matrix (ι × κ) (ι × κ) ℂ) (i : Fin (q + 1)) :
    (A.postUnitary V).stateAt O i =
      if i = Fin.last q then act (V : Matrix _ _ ℂ) (A.stateAt O i)
      else A.stateAt O i := by
  induction i using Fin.induction with
  | zero =>
    change act (↑(if (0 : Fin (q + 1)) = Fin.last q then V * A.U 0 else A.U 0))
      A.start = if (0 : Fin (q + 1)) = Fin.last q
      then act (V : Matrix _ _ ℂ) (act (A.U 0 : Matrix _ _ ℂ) A.start)
      else act (A.U 0 : Matrix _ _ ℂ) A.start
    split_ifs
    · exact act_mul_eq _ _ _
    · rfl
  | succ i ih =>
    have hprev : i.castSucc ≠ Fin.last q := by
      intro he
      have := congrArg Fin.val he
      have := i.isLt
      simp only [Fin.val_castSucc, Fin.val_last] at *
      omega
    rw [if_neg hprev] at ih
    change act (((A.postUnitary V).U i.succ : Matrix _ _ ℂ))
      (act (Matrix.kronecker O (1 : Matrix W W ℂ))
        ((A.postUnitary V).stateAt O i.castSucc)) = _
    rw [ih]
    change act (↑(if i.succ = Fin.last q then V * A.U i.succ else A.U i.succ))
      (act (Matrix.kronecker O (1 : Matrix W W ℂ)) (A.stateAt O i.castSucc)) =
      if i.succ = Fin.last q then act (V : Matrix _ _ ℂ)
        (act (A.U i.succ : Matrix _ _ ℂ)
          (act (Matrix.kronecker O (1 : Matrix W W ℂ)) (A.stateAt O i.castSucc)))
      else act (A.U i.succ : Matrix _ _ ℂ)
          (act (Matrix.kronecker O (1 : Matrix W W ℂ)) (A.stateAt O i.castSucc))
    split_ifs
    · exact act_mul_eq _ _ _
    · rfl

theorem finalState_postUnitary (A : QueryAlg ι κ W q)
    (V : Matrix.unitaryGroup ((ι × κ) × W) ℂ)
    (O : Matrix (ι × κ) (ι × κ) ℂ) :
    (A.postUnitary V).finalState O = act (V : Matrix _ _ ℂ) (A.finalState O) := by
  simp [finalState, stateAt_postUnitary]

noncomputable def snoc (A : QueryAlg ι κ W q)
    (V : Matrix.unitaryGroup ((ι × κ) × W) ℂ) : QueryAlg ι κ W (q + 1) where
  start := A.start
  start_unit := A.start_unit
  U := Fin.lastCases V A.U

theorem stateAt_snoc_castSucc (A : QueryAlg ι κ W q)
    (V : Matrix.unitaryGroup ((ι × κ) × W) ℂ)
    (O : Matrix (ι × κ) (ι × κ) ℂ) (i : Fin (q + 1)) :
    (A.snoc V).stateAt O i.castSucc = A.stateAt O i := by
  induction i using Fin.induction with
  | zero =>
    change act (((A.snoc V).U (Fin.castSucc 0) : Matrix _ _ ℂ)) A.start = _
    simp only [snoc, Fin.lastCases_castSucc]
    rfl
  | succ i ih =>
    rw [Fin.castSucc_succ]
    simp only [stateAt, Fin.induction_succ]
    change act (((A.snoc V).U i.succ.castSucc : Matrix _ _ ℂ))
      (act (Matrix.kronecker O (1 : Matrix W W ℂ))
        ((A.snoc V).stateAt O i.castSucc.castSucc)) =
      act (A.U i.succ : Matrix _ _ ℂ)
        (act (Matrix.kronecker O (1 : Matrix W W ℂ)) (A.stateAt O i.castSucc))
    rw [ih]
    simp only [snoc, Fin.lastCases_castSucc]

theorem finalState_snoc (A : QueryAlg ι κ W q)
    (V : Matrix.unitaryGroup ((ι × κ) × W) ℂ)
    (O : Matrix (ι × κ) (ι × κ) ℂ) :
    (A.snoc V).finalState O = act (V : Matrix _ _ ℂ)
      (act (Matrix.kronecker O (1 : Matrix W W ℂ)) (A.finalState O)) := by
  change (A.snoc V).stateAt O (Fin.last q).succ = _
  simp only [stateAt, Fin.induction_succ]
  change act (((A.snoc V).U (Fin.last (q + 1)) : Matrix _ _ ℂ))
    (act (Matrix.kronecker O (1 : Matrix W W ℂ))
      ((A.snoc V).stateAt O (Fin.last q).castSucc)) = _
  rw [stateAt_snoc_castSucc]
  simp [snoc, finalState]

noncomputable def appendQueries (A : QueryAlg ι κ W q) :
    (r : ℕ) → (Fin r → Matrix.unitaryGroup ((ι × κ) × W) ℂ) → QueryAlg ι κ W (q + r)
  | 0, _ => A
  | r + 1, V => (appendQueries A r (fun i => V i.castSucc)).snoc (V (Fin.last r))

theorem finalState_appendQueries_zero (A : QueryAlg ι κ W q)
    (V : Fin 0 → Matrix.unitaryGroup ((ι × κ) × W) ℂ)
    (O : Matrix (ι × κ) (ι × κ) ℂ) :
    (A.appendQueries 0 V).finalState O = A.finalState O := rfl

theorem finalState_appendQueries_succ (A : QueryAlg ι κ W q) (r : ℕ)
    (V : Fin (r + 1) → Matrix.unitaryGroup ((ι × κ) × W) ℂ)
    (O : Matrix (ι × κ) (ι × κ) ℂ) :
    (A.appendQueries (r + 1) V).finalState O = act (V (Fin.last r) : Matrix _ _ ℂ)
      (act (Matrix.kronecker O (1 : Matrix W W ℂ))
        ((A.appendQueries r (fun i => V i.castSucc)).finalState O)) :=
  finalState_snoc _ _ _

end QAlgorithms.QueryAlg

end


-- Solutions.QueryBatchLinear
section

namespace QAlgorithms.QueryBatchLinear

section Permutations

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def permUnitary (e : Equiv.Perm α) : Matrix.unitaryGroup α ℂ :=
  ⟨(e⁻¹).permMatrix ℂ, by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
    rw [Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul]
    simp⟩

theorem act_perm_apply (e : Equiv.Perm α) (ψ : EuclideanSpace ℂ α) (x : α) :
    act (permUnitary e : Matrix α α ℂ) ψ x = ψ (e.symm x) := by
  change Matrix.mulVec ((e⁻¹).permMatrix ℂ) (WithLp.ofLp ψ) x = _
  rw [Matrix.permMatrix_mulVec]
  rfl

theorem act_perm_at (e : Equiv.Perm α) (ψ : EuclideanSpace ℂ α) (x : α) :
    act (permUnitary e : Matrix α α ℂ) ψ (e x) = ψ x := by
  simp [act_perm_apply]

end Permutations

section Embeddings

variable {α β : Type*} [Fintype α] [Fintype β]

noncomputable def embedState (e : α → β) (ψ : EuclideanSpace ℂ α) : EuclideanSpace ℂ β :=
  WithLp.toLp 2 (Function.extend e ψ 0)

theorem embedState_apply (e : α → β) (he : Function.Injective e)
    (ψ : EuclideanSpace ℂ α) (x : α) : embedState e ψ (e x) = ψ x :=
  he.extend_apply _ _ _

theorem embedState_zero (e : α → β) (ψ : EuclideanSpace ℂ α) (y : β)
    (hy : y ∉ Set.range e) : embedState e ψ y = 0 :=
  Function.extend_apply' _ _ _ hy

theorem embedState_norm (e : α → β) (he : Function.Injective e)
    (ψ : EuclideanSpace ℂ α) : ‖embedState e ψ‖ = ‖ψ‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.norm_sq_eq]
  symm
  exact Fintype.sum_of_injective e he _ _
    (fun y hy => by simp [embedState_zero e ψ y hy])
    (fun x => by rw [embedState_apply e he])

theorem eq_embedState (e : α → β) (he : Function.Injective e)
    (ψ : EuclideanSpace ℂ α) (φ : EuclideanSpace ℂ β)
    (hat : ∀ x, φ (e x) = ψ x) (hoff : ∀ y ∉ Set.range e, φ y = 0) :
    φ = embedState e ψ := by
  ext y
  by_cases hy : y ∈ Set.range e
  · obtain ⟨x, rfl⟩ := hy
    rw [hat, embedState_apply e he]
  · rw [hoff y hy, embedState_zero e ψ y hy]

theorem probEvent_embedState [DecidableEq α] [DecidableEq β]
    (e : α → β) (he : Function.Injective e) (ψ : EuclideanSpace ℂ α)
    (P : β → Prop) [DecidablePred P] :
    probEvent (embedState e ψ) P = probEvent ψ (fun x => P (e x)) := by
  simp only [probEvent, prob, QAlgorithms.ket, EuclideanSpace.inner_single_left,
    one_mul, Finset.sum_filter]
  symm
  exact Fintype.sum_of_injective e he _ _
    (fun y hy => by simp [embedState_zero e ψ y hy])
    (fun x => by rw [embedState_apply e he])

theorem probEvent_eq_of_injective_support [DecidableEq α] [DecidableEq β]
    (e : α → β) (he : Function.Injective e)
    (ψ : EuclideanSpace ℂ α) (φ : EuclideanSpace ℂ β)
    (hat : ∀ x, φ (e x) = ψ x) (hoff : ∀ y ∉ Set.range e, φ y = 0)
    (P : β → Prop) [DecidablePred P] :
    probEvent φ P = probEvent ψ (fun x => P (e x)) := by
  rw [eq_embedState e he ψ φ hat hoff]
  exact probEvent_embedState e he ψ P

theorem act_perm_embedState [DecidableEq β]
    (e : α → β) (he : Function.Injective e) (p : Equiv.Perm β)
    (ψ : EuclideanSpace ℂ α) :
    act (permUnitary p : Matrix β β ℂ) (embedState e ψ) = embedState (p ∘ e) ψ := by
  apply eq_embedState (p ∘ e) (p.injective.comp he)
  · intro x
    rw [Function.comp_apply, act_perm_at, embedState_apply e he]
  · intro y hy
    rw [act_perm_apply]
    apply embedState_zero
    rintro ⟨x, hx⟩
    apply hy
    exact ⟨x, by simpa [Function.comp_apply] using congrArg p hx⟩

end Embeddings

section Tensor

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

theorem kronecker_one_unitary {U : Matrix α α ℂ}
    (hU : U ∈ Matrix.unitaryGroup α ℂ) :
    Matrix.kronecker U (1 : Matrix β β ℂ) ∈ Matrix.unitaryGroup (α × β) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff] at hU ⊢
  simp only [Matrix.kronecker, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]
  rw [← Matrix.mul_kronecker_mul]
  simp only [← Matrix.star_eq_conjTranspose, hU, one_mul, Matrix.one_kronecker_one]

noncomputable def tensorUnitary (U : Matrix.unitaryGroup α ℂ) :
    Matrix.unitaryGroup (α × β) ℂ := ⟨_, kronecker_one_unitary U.property⟩

theorem act_tensor_apply (U : Matrix α α ℂ) (ψ : EuclideanSpace ℂ (α × β))
    (a : α) (b : β) :
    act (Matrix.kronecker U (1 : Matrix β β ℂ)) ψ (a, b) = ∑ x, U a x * ψ (x, b) := by
  simp [act, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.one_apply]

theorem act_tensor_embedState (U : Matrix α α ℂ) (ψ : EuclideanSpace ℂ α) (b : β) :
    act (Matrix.kronecker U (1 : Matrix β β ℂ)) (embedState (fun a => (a, b)) ψ) =
      embedState (fun a => (a, b)) (act U ψ) := by
  have hinj : Function.Injective (fun a : α => (a, b)) := fun _ _ h => (Prod.mk.inj h).1
  apply eq_embedState _ hinj
  · intro a
    rw [act_tensor_apply]
    simp only [embedState_apply (fun a : α => (a, b)) hinj]
    rfl
  · rintro ⟨a, b'⟩ h
    rw [act_tensor_apply]
    apply Finset.sum_eq_zero
    intro x _
    rw [embedState_zero]
    · simp
    · rintro ⟨x', hx⟩
      apply h
      exact ⟨a, by simpa using congrArg (fun p : α × β => (a, p.2)) hx⟩

end Tensor

section Oracle

variable {ι κ W : Type*} [Fintype ι] [Fintype κ] [Fintype W]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq W] [AddCommGroup κ]

def queryPerm (f : ι → κ) : Equiv.Perm ((ι × κ) × W) where
  toFun p := ((p.1.1, p.1.2 + f p.1.1), p.2)
  invFun p := ((p.1.1, p.1.2 - f p.1.1), p.2)
  left_inv := by rintro ⟨⟨i, y⟩, w⟩; simp
  right_inv := by rintro ⟨⟨i, y⟩, w⟩; simp

theorem act_xor_tensor_apply (f : ι → κ) (ψ : EuclideanSpace ℂ ((ι × κ) × W))
    (i : ι) (y : κ) (w : W) :
    act (Matrix.kronecker (xorOracle f) (1 : Matrix W W ℂ)) ψ ((i, y), w) =
      ψ ((i, y - f i), w) := by
  rw [act_tensor_apply]
  simp only [xorOracle, Matrix.of_apply]
  rw [Finset.sum_eq_single (i, y - f i)]
  · simp
  · rintro ⟨j, z⟩ _ hne
    by_cases hij : i = j
    · subst j
      have hy : y ≠ z + f i := by
        intro he
        apply hne
        exact Prod.ext rfl (by rw [he]; simp)
      simp [hy]
    · simp [hij]
  · simp

theorem act_xor_eq_perm (f : ι → κ) (ψ : EuclideanSpace ℂ ((ι × κ) × W)) :
    act (Matrix.kronecker (xorOracle f) (1 : Matrix W W ℂ)) ψ =
      act (permUnitary (queryPerm (W := W) f) : Matrix _ _ ℂ) ψ := by
  ext p
  obtain ⟨⟨i, y⟩, w⟩ := p
  rw [act_xor_tensor_apply, act_perm_apply]
  rfl

end Oracle

end QAlgorithms.QueryBatchLinear

end


-- Solutions.QueryAlgLift
section

namespace QAlgorithms.QueryAlg

open QueryBatchLinear

section Matrices

variable {Q W D : Type*} [Fintype Q] [Fintype W] [Fintype D]
  [DecidableEq Q] [DecidableEq W] [DecidableEq D]

noncomputable def liftMatrix (M : Matrix (Q × W) (Q × W) ℂ) :
    Matrix (Q × (W × D)) (Q × (W × D)) ℂ :=
  (Matrix.kronecker M (1 : Matrix D D ℂ)).submatrix
    (Equiv.prodAssoc Q W D).symm (Equiv.prodAssoc Q W D).symm

theorem liftMatrix_unitary (U : Matrix.unitaryGroup (Q × W) ℂ) :
    liftMatrix (D := D) (U : Matrix (Q × W) (Q × W) ℂ) ∈
      Matrix.unitaryGroup (Q × (W × D)) ℂ := by
  have h := kronecker_one_unitary (β := D) U.property
  rw [Matrix.mem_unitaryGroup_iff] at h ⊢
  simp only [liftMatrix, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix]
  rw [Matrix.submatrix_mul_equiv]
  rw [← Matrix.star_eq_conjTranspose, h]
  exact Matrix.submatrix_one_equiv _

noncomputable def liftUnitary (U : Matrix.unitaryGroup (Q × W) ℂ) :
    Matrix.unitaryGroup (Q × (W × D)) ℂ := ⟨_, liftMatrix_unitary U⟩

theorem act_liftMatrix_apply (M : Matrix (Q × W) (Q × W) ℂ)
    (ψ : EuclideanSpace ℂ (Q × (W × D))) (a : Q) (b : W) (d : D) :
    act (liftMatrix M) ψ (a, (b, d)) =
      ∑ x : Q × W, M (a, b) x * ψ (x.1, (x.2, d)) := by
  simp [act, liftMatrix, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply, Matrix.submatrix]

def ancillaBasis (d : D) (z : Q × W) : Q × (W × D) := (z.1, (z.2, d))

theorem ancillaBasis_injective (d : D) : Function.Injective (ancillaBasis (Q := Q) (W := W) d) := by
  rintro ⟨x, w⟩ ⟨x', w'⟩ h
  simpa [ancillaBasis] using h

theorem act_liftMatrix_embed (M : Matrix (Q × W) (Q × W) ℂ)
    (ψ : EuclideanSpace ℂ (Q × W)) (d : D) :
    act (liftMatrix M) (embedState (ancillaBasis d) ψ) =
      embedState (ancillaBasis d) (act M ψ) := by
  apply eq_embedState _ (ancillaBasis_injective d)
  · rintro ⟨a, b⟩
    rw [ancillaBasis, act_liftMatrix_apply]
    change (∑ x : Q × W, M (a, b) x * embedState (ancillaBasis d) ψ (ancillaBasis d x)) = _
    simp only [embedState_apply _ (ancillaBasis_injective d)]
    rfl
  · rintro ⟨a, b, d'⟩ h
    rw [act_liftMatrix_apply]
    apply Finset.sum_eq_zero
    intro x _
    rw [embedState_zero]
    · simp
    · rintro ⟨y, hy⟩
      apply h
      have hd : d = d' := congrArg (fun p : Q × (W × D) => p.2.2) hy
      exact ⟨(a, b), by simp [ancillaBasis, hd]⟩

theorem liftMatrix_oracle (O : Matrix Q Q ℂ) :
    liftMatrix (D := D) (Matrix.kronecker O (1 : Matrix W W ℂ)) =
      Matrix.kronecker O (1 : Matrix (W × D) (W × D) ℂ) := by
  ext ⟨x, w, d⟩ ⟨x', w', d'⟩
  simp only [liftMatrix, Matrix.submatrix_apply, Equiv.prodAssoc_symm_apply,
    Matrix.kroneckerMap_apply, Matrix.one_apply, Prod.mk.injEq]
  by_cases hw : w = w' <;> by_cases hd : d = d' <;> simp [hw, hd]

end Matrices

variable {ι κ W D : Type*} [Fintype ι] [Fintype κ] [Fintype W] [Fintype D]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq W] [DecidableEq D] {q : ℕ}

noncomputable def liftAncilla (A : QueryAlg ι κ W q) (d : D) : QueryAlg ι κ (W × D) q where
  start := embedState (ancillaBasis d) A.start
  start_unit := by rw [embedState_norm _ (ancillaBasis_injective d), A.start_unit]
  U i := liftUnitary (A.U i)

theorem stateAt_liftAncilla (A : QueryAlg ι κ W q) (d : D)
    (O : Matrix (ι × κ) (ι × κ) ℂ) (i : Fin (q + 1)) :
    (A.liftAncilla d).stateAt O i = embedState (ancillaBasis d) (A.stateAt O i) := by
  induction i using Fin.induction with
  | zero => exact act_liftMatrix_embed (A.U 0 : Matrix ((ι × κ) × W) ((ι × κ) × W) ℂ) A.start d
  | succ i ih =>
    change act (liftMatrix (A.U i.succ : Matrix ((ι × κ) × W) ((ι × κ) × W) ℂ))
      (act (Matrix.kronecker O (1 : Matrix (W × D) (W × D) ℂ))
        ((A.liftAncilla d).stateAt O i.castSucc)) = _
    rw [ih, ← liftMatrix_oracle, act_liftMatrix_embed, act_liftMatrix_embed]
    rfl

theorem finalState_liftAncilla (A : QueryAlg ι κ W q) (d : D)
    (O : Matrix (ι × κ) (ι × κ) ℂ) :
    (A.liftAncilla d).finalState O = embedState (ancillaBasis d) (A.finalState O) :=
  stateAt_liftAncilla A d O _

end QAlgorithms.QueryAlg

end


-- Solutions.QueryBatchRealization
section

namespace QAlgorithms.QueryBatchRealization

open QueryBatchLinear
open scoped Classical

set_option linter.unusedSectionVars false

variable {ι κ W : Type*} [Fintype ι] [Fintype κ] [Fintype W]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq W] [AddCommGroup κ]

abbrev Original (ι κ W : Type*) := (ι × κ) × W
abbrev Work (ι κ W : Type*) (r : ℕ) := W × ((ι × κ) × (Fin r → κ))
abbrev Register (ι κ W : Type*) (r : ℕ) := (ι × κ) × Work ι κ W r

def stored {r : ℕ} (p : Register ι κ W r) : Original ι κ W :=
  (p.2.2.1, p.2.1)

def ready {r : ℕ} (i₀ : ι) (z : Original ι κ W) (d : Fin r → κ) :
    Register ι κ W r := ((i₀, 0), (z.2, (z.1, d)))

lemma stored_ready {r : ℕ} (i₀ : ι) (z : Original ι κ W) (d : Fin r → κ) :
    stored (ready i₀ z d) = z := by cases z; rfl

lemma ready_injective {r : ℕ} (i₀ : ι) (d : Original ι κ W → Fin r → κ) :
    Function.Injective (fun z => ready i₀ z (d z)) := by
  intro z z' h
  have := congrArg stored h
  simpa only [stored_ready] using this

def swapSaved (r : ℕ) : Equiv.Perm (Register ι κ W r) where
  toFun p := (p.2.2.1, (p.2.1, (p.1, p.2.2.2)))
  invFun p := (p.2.2.1, (p.2.1, (p.1, p.2.2.2)))
  left_inv p := by rfl
  right_inv p := by rfl

def inputSwap {r : ℕ} (i₀ : ι) (addr : Original ι κ W → Fin r → ι) (j : Fin r) :
    Equiv.Perm (Register ι κ W r) where
  toFun p := ((Equiv.swap i₀ (addr (stored p) j) p.1.1, p.1.2), p.2)
  invFun p := ((Equiv.swap i₀ (addr (stored p) j) p.1.1, p.1.2), p.2)
  left_inv p := by
    rcases p with ⟨⟨i, a⟩, w, s, d⟩
    simp [stored]
  right_inv p := by
    rcases p with ⟨⟨i, a⟩, w, s, d⟩
    simp [stored]

def exchangeAnswer {r : ℕ} (j : Fin r) : Equiv.Perm (Register ι κ W r) where
  toFun p := ((p.1.1, p.2.2.2 j), (p.2.1, (p.2.2.1, Function.update p.2.2.2 j p.1.2)))
  invFun p := ((p.1.1, p.2.2.2 j), (p.2.1, (p.2.2.1, Function.update p.2.2.2 j p.1.2)))
  left_inv p := by
    rcases p with ⟨⟨i, a⟩, w, s, d⟩
    simp
  right_inv p := by
    rcases p with ⟨⟨i, a⟩, w, s, d⟩
    simp

def prepare {r : ℕ} (i₀ : ι) (addr : Original ι κ W → Fin r → ι) (j : Fin r) :
    Equiv.Perm (Register ι κ W r) :=
  (inputSwap i₀ addr j).trans (exchangeAnswer j)

def queryMap {r : ℕ} (f : ι → κ) (p : Register ι κ W r) : Register ι κ W r :=
  ((p.1.1, p.1.2 + f p.1.1), p.2)

lemma stage_ready {r : ℕ} (i₀ : ι) (addr : Original ι κ W → Fin r → ι)
    (j : Fin r) (f : ι → κ) (z : Original ι κ W) (d : Fin r → κ) :
    (prepare i₀ addr j).symm (queryMap f (prepare i₀ addr j (ready i₀ z d))) =
      ready i₀ z (Function.update d j (d j + f (addr z j))) := by
  rcases z with ⟨⟨i, a⟩, w⟩
  simp [prepare, inputSwap, exchangeAnswer, ready, stored, queryMap,
    Equiv.trans_apply, Function.update_idem]

def ledger {r : ℕ} (addr : Original ι κ W → Fin r → ι) (f : ι → κ)
    (t : ℕ) (z : Original ι κ W) : Fin r → κ :=
  fun k => if k.val < t then f (addr z k) else 0

lemma ledger_zero {r : ℕ} (addr : Original ι κ W → Fin r → ι) (f : ι → κ)
    (z : Original ι κ W) : ledger addr f 0 z = 0 := by
  funext k
  simp [ledger]

lemma ledger_all {r : ℕ} (addr : Original ι κ W → Fin r → ι) (f : ι → κ)
    (z : Original ι κ W) : ledger addr f r z = fun k => f (addr z k) := by
  funext k
  simp [ledger, k.isLt]

lemma ledger_step {r t : ℕ} (addr : Original ι κ W → Fin r → ι) (f : ι → κ)
    (z : Original ι κ W) (ht : t < r) :
    Function.update (ledger addr f t z) ⟨t, ht⟩
      (ledger addr f t z ⟨t, ht⟩ + f (addr z ⟨t, ht⟩)) = ledger addr f (t + 1) z := by
  funext k
  by_cases hk : k = ⟨t, ht⟩
  · subst k
    simp [ledger]
  · have hkt : k.val ≠ t := by
      intro h
      exact hk (Fin.ext h)
    have hlt : (k.val < t + 1) ↔ k.val < t := by omega
    simp [Function.update_of_ne hk, ledger, hlt]

lemma stage_ledger {r t : ℕ} (i₀ : ι) (addr : Original ι κ W → Fin r → ι)
    (f : ι → κ) (z : Original ι κ W) (ht : t < r) :
    (prepare i₀ addr ⟨t, ht⟩).symm
      (queryMap f (prepare i₀ addr ⟨t, ht⟩ (ready i₀ z (ledger addr f t z)))) =
      ready i₀ z (ledger addr f (t + 1) z) := by
  rw [stage_ready, ledger_step]

/-- One prepared query records the next answer and restores the active query register. -/
lemma stage_action {r t : ℕ} (i₀ : ι)
    (addr : Original ι κ W → Fin r → ι) (f : ι → κ)
    (ψ : EuclideanSpace ℂ (Original ι κ W)) (ht : t < r) :
    act (permUnitary (prepare i₀ addr ⟨t, ht⟩).symm : Matrix _ _ ℂ)
      (act (Matrix.kronecker (xorOracle f)
          (1 : Matrix (Work ι κ W r) (Work ι κ W r) ℂ))
        (act (permUnitary (prepare i₀ addr ⟨t, ht⟩) : Matrix _ _ ℂ)
          (embedState (fun z => ready i₀ z (ledger addr f t z)) ψ))) =
      embedState (fun z => ready i₀ z (ledger addr f (t + 1) z)) ψ := by
  rw [act_perm_embedState _ (ready_injective i₀ _)]
  rw [act_xor_eq_perm, act_perm_embedState _
    ((prepare i₀ addr ⟨t, ht⟩).injective.comp (ready_injective i₀ _))]
  rw [act_perm_embedState _
    ((queryPerm (W := Work ι κ W r) f).injective.comp
      ((prepare i₀ addr ⟨t, ht⟩).injective.comp (ready_injective i₀ _)))]
  congr 1
  funext z
  exact stage_ledger i₀ addr f z ht

/-- A query algorithm coherently records any prefix of a fixed batch of addresses.
The witnesses are chosen before the oracle function is supplied. -/
theorem realize_prefix {q r : ℕ} (i₀ : ι) (A : QueryAlg ι κ W q)
    (addr : Original ι κ W → Fin r → ι) :
    ∀ t, t ≤ r → ∃ B : QueryAlg ι κ (Work ι κ W r) (q + t),
      ∀ f : ι → κ, B.finalState (xorOracle f) =
        embedState (fun z => ready i₀ z (ledger addr f t z))
          (A.finalState (xorOracle f)) := by
  intro t
  induction t with
  | zero =>
    intro _
    refine ⟨(A.liftAncilla ((i₀, 0), (0 : Fin r → κ))).postUnitary
      (permUnitary (swapSaved r)), ?_⟩
    intro f
    rw [QueryAlg.finalState_postUnitary, QueryAlg.finalState_liftAncilla,
      act_perm_embedState _ (QueryAlg.ancillaBasis_injective _)]
    congr 1
  | succ t ih =>
    intro ht
    obtain ⟨B, hB⟩ := ih (by omega)
    have htr : t < r := by omega
    refine ⟨(B.postUnitary (permUnitary (prepare i₀ addr ⟨t, htr⟩))).snoc
      (permUnitary (prepare i₀ addr ⟨t, htr⟩).symm), ?_⟩
    intro f
    rw [QueryAlg.finalState_snoc, QueryAlg.finalState_postUnitary, hB]
    exact stage_action i₀ addr f _ htr

/-- Deferred measurement followed by a fixed finite batch of oracle queries has
an exact realization in the unitary query model, with one query per batch entry. -/
theorem batch_realization {q r : ℕ} (i₀ : ι) (A : QueryAlg ι κ W q)
    (addr : Original ι κ W → Fin r → ι)
    (test : Original ι κ W → (Fin r → κ) → Prop) :
    ∃ (B : QueryAlg ι κ (Work ι κ W r) (q + r))
      (acc : Register ι κ W r → Prop),
      ∀ f : ι → κ,
        probEvent (B.finalState (xorOracle f)) acc =
          probEvent (A.finalState (xorOracle f))
            (fun z => test z (fun j => f (addr z j))) := by
  obtain ⟨B, hB⟩ := realize_prefix i₀ A addr r le_rfl
  refine ⟨B, fun p => test (stored p) p.2.2.2, ?_⟩
  intro f
  rw [hB, probEvent_embedState _ (ready_injective i₀ _)]
  simp only [ready, stored, ledger_all, Prod.mk.eta]

end QAlgorithms.QueryBatchRealization

end


-- Solutions.WeldedPathVerifierBatch
section

namespace WeldedPath.VerifierBatch

open QAlgorithms Supplement

lemma bitsToNat_zero (d : ℕ) : bitsToNat (0 : Qubits d) = 0 := by
  simp [bitsToNat]

lemma bitsToNat_natToBits (d k : ℕ) : bitsToNat (natToBits d k) = k % 2 ^ d := by
  rw [← bitsEquivFin_apply]
  simp [natToBits]

def labelBits {n : ℕ} (xs : List (Fin 3 × Qubits (2 * n + 1))) (i : ℕ) :
    Qubits (2 * n + 1) :=
  if i = 0 then 0 else (xs.getD (i - 1) (0, 0)).2

lemma labelBits_decode {n : ℕ} (xs : List (Fin 3 × Qubits (2 * n + 1))) (i : ℕ) :
    bitsToNat (labelBits xs i) = (pathLabels xs).getD i 0 := by
  cases i with
  | zero => simp [labelBits, pathLabels, bitsToNat_zero]
  | succ i =>
    simp only [labelBits, Nat.succ_ne_zero, if_false, Nat.add_one_sub_one, pathLabels,
      List.getD_cons_succ]
    simpa only [bitsToNat_zero] using
      (List.getD_map xs (0, 0) (fun s : Fin 3 × Qubits (2 * n + 1) => bitsToNat s.2)).symm

lemma getD_le {xs : List ℕ} {M : ℕ} (h : ∀ x ∈ xs, x ≤ M) (i : ℕ) :
    xs.getD i 0 ≤ M := by
  induction xs generalizing i with
  | nil => simp
  | cons x xs ih =>
    cases i with
    | zero => exact h x (by simp)
    | succ i => exact ih (fun y hy => h y (by simp [hy])) i

lemma candidate_label_bound {n : ℕ} {xs : List (Fin 3 × Qubits (2 * n + 1))}
    (hc : IsCandidatePath xs) (i : ℕ) : (pathLabels xs).getD i 0 ≤ labelBound n := by
  apply getD_le
  intro z hz
  rcases List.mem_cons.mp hz with rfl | hz
  · omega
  · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hz
    exact hc.1 s hs

lemma label_fits (n : ℕ) (z : Label n) : z.val < 2 ^ (2 * n + 1) := by
  have hz : z.val ≤ 2 ^ (2 * n) := Nat.le_of_lt_succ z.isLt
  have hp := Nat.two_pow_pos (2 * n)
  rw [pow_succ]
  omega

lemma oracleFn_decode {n l : ℕ} (G : WeldedInstance n)
    (σ : Equiv.Perm (Label n) × Equiv.Perm G.edges)
    (b : Qubits (2 * n + 1)) (α : Fin 3) (hb : bitsToNat b ≤ labelBound n) :
    bitsToNat (G.oracleFn l σ (b, α)) = Fnat l G σ (bitsToNat b) α := by
  have hb' : bitsToNat b < labelBound n + 1 := by omega
  simp only [WeldedInstance.oracleFn, dif_pos hb', bitsToNat_natToBits, Fnat]
  apply Nat.mod_eq_of_lt
  change (G.F l σ ⟨bitsToNat b, hb'⟩ α).val < 2 ^ (2 * n + 1)
  exact label_fits n _

lemma oracle_label_decode {n l : ℕ} (G : WeldedInstance n)
    (σ : Equiv.Perm (Label n) × Equiv.Perm G.edges)
    (xs : List (Fin 3 × Qubits (2 * n + 1))) (hc : IsCandidatePath xs)
    (i : ℕ) (α : Fin 3) :
    bitsToNat (G.oracleFn l σ (labelBits xs i, α)) =
      Fnat l G σ ((pathLabels xs).getD i 0) α := by
  rw [oracleFn_decode G σ _ _ (by rw [labelBits_decode]; exact candidate_label_bound hc i),
    labelBits_decode]

def addr {n : ℕ} (q : ℕ) (xs : List (Fin 3 × Qubits (2 * n + 1)))
    (j : Fin (6 * q + 3)) : Qubits (2 * n + 1) × Fin 3 :=
  if xs.length ≤ 2 * q + 1 then
    if j.val < xs.length then (labelBits xs j.val, (xs.getD j.val (0, 0)).1)
    else (labelBits xs xs.length, ⟨(j.val - xs.length) % 3, Nat.mod_lt _ (by decide)⟩)
  else (labelBits xs (j.val / 3 + 1), ⟨j.val % 3, Nat.mod_lt _ (by decide)⟩)

def edgeSlot (q : ℕ) (hq : 1 ≤ q) (m : ℕ) (hm : m ≤ 2 * q + 1)
    (i : ℕ) (hi : i < m) : Fin (6 * q + 3) := ⟨i, by omega⟩

def endSlot (q : ℕ) (hq : 1 ≤ q) (m : ℕ) (hm : m ≤ 2 * q + 1)
    (α : Fin 3) : Fin (6 * q + 3) := ⟨m + α.val, by have := α.isLt; omega⟩

def longSlot (q : ℕ) (i : ℕ) (hi : 1 ≤ i) (hi' : i ≤ 2 * q + 1)
    (α : Fin 3) : Fin (6 * q + 3) := ⟨3 * (i - 1) + α.val, by have := α.isLt; omega⟩

open Classical in
def test {n : ℕ} (q : ℕ) (hq : 1 ≤ q)
    (xs : List (Fin 3 × Qubits (2 * n + 1)))
    (answers : Fin (6 * q + 3) → Qubits (2 * n + 1)) : Prop :=
  IsCandidatePath xs ∧
    (∀ hs : xs.length ≤ 2 * q + 1,
      (∀ (i : ℕ) (hi : i < xs.length),
        bitsToNat (answers (edgeSlot q hq xs.length hs i hi)) = (pathLabels xs).getD (i + 1) 0) ∧
      (Finset.univ.filter fun α : Fin 3 =>
        bitsToNat (answers (endSlot q hq xs.length hs α)) ≠
          (pathLabels xs).getD xs.length 0).card = 2) ∧
    (∀ _ : 2 * q + 1 < xs.length, ∀ (i : ℕ) (hi : 1 ≤ i) (hi' : i ≤ 2 * q + 1),
      ∃ α : Fin 3, bitsToNat (answers (longSlot q i hi hi' α)) ≠
        (pathLabels xs).getD i 0)

lemma addr_edge {n q : ℕ} (hq : 1 ≤ q)
    (xs : List (Fin 3 × Qubits (2 * n + 1))) (hs : xs.length ≤ 2 * q + 1)
    (i : ℕ) (hi : i < xs.length) :
    addr q xs (edgeSlot q hq xs.length hs i hi) =
      (labelBits xs i, (xs.getD i (0, 0)).1) := by
  change addr q xs ⟨i, _⟩ = _
  simp [addr, hs, hi]

lemma addr_end {n q : ℕ} (hq : 1 ≤ q)
    (xs : List (Fin 3 × Qubits (2 * n + 1))) (hs : xs.length ≤ 2 * q + 1)
    (α : Fin 3) :
    addr q xs (endSlot q hq xs.length hs α) = (labelBits xs xs.length, α) := by
  change addr q xs ⟨xs.length + α.val, _⟩ = _
  simp only [addr, if_pos hs]
  rw [if_neg (by omega : ¬ xs.length + α.val < xs.length)]
  congr 1
  apply Fin.ext
  change (xs.length + α.val - xs.length) % 3 = α.val
  simp [Nat.mod_eq_of_lt α.isLt]

lemma addr_long {n q : ℕ} (xs : List (Fin 3 × Qubits (2 * n + 1)))
    (hs : 2 * q + 1 < xs.length) (i : ℕ) (hi : 1 ≤ i) (hi' : i ≤ 2 * q + 1)
    (α : Fin 3) :
    addr q xs (longSlot q i hi hi' α) = (labelBits xs i, α) := by
  simp only [addr, longSlot, if_neg (by omega : ¬ xs.length ≤ 2 * q + 1)]
  have hd : (3 * (i - 1) + α.val) / 3 + 1 = i := by have := α.isLt; omega
  rw [hd]
  congr 1
  apply Fin.ext
  change (3 * (i - 1) + α.val) % 3 = α.val
  have := α.isLt
  omega

theorem test_oracle_iff {n : ℕ} (l : ℕ) (G : WeldedInstance n)
    (σ : Equiv.Perm (Label n) × Equiv.Perm G.edges)
    (q : ℕ) (hq : 1 ≤ q) (xs : List (Fin 3 × Qubits (2 * n + 1))) :
    test q hq xs (fun j => G.oracleFn l σ (addr q xs j)) ↔ Accepts39 l G σ q xs := by
  classical
  unfold test Accepts39
  dsimp only
  apply and_congr_right
  intro hc
  have he : ∀ (hs : xs.length ≤ 2 * q + 1) (i : ℕ) (hi : i < xs.length),
      bitsToNat (G.oracleFn l σ (addr q xs (edgeSlot q hq xs.length hs i hi))) =
        Fnat l G σ ((pathLabels xs).getD i 0) ((xs.getD i (0, 0)).1) := by
    intro hs i hi
    rw [addr_edge hq xs hs i hi, oracle_label_decode G σ xs hc]
  have hend : ∀ (hs : xs.length ≤ 2 * q + 1) (α : Fin 3),
      bitsToNat (G.oracleFn l σ (addr q xs (endSlot q hq xs.length hs α))) =
        Fnat l G σ ((pathLabels xs).getD xs.length 0) α := by
    intro hs α
    rw [addr_end hq xs hs α, oracle_label_decode G σ xs hc]
  have hl : ∀ (hs : 2 * q + 1 < xs.length) (i : ℕ) (hi : 1 ≤ i) (hi' : i ≤ 2 * q + 1)
      (α : Fin 3),
      bitsToNat (G.oracleFn l σ (addr q xs (longSlot q i hi hi' α))) =
        Fnat l G σ ((pathLabels xs).getD i 0) α := by
    intro hs i hi hi' α
    rw [addr_long xs hs i hi hi' α, oracle_label_decode G σ xs hc]
  constructor
  · rintro ⟨hshort, hlong⟩
    constructor
    · intro hs
      obtain ⟨hedge, hend'⟩ := hshort hs
      constructor
      · intro i hi
        simpa only [he hs i hi] using hedge i hi
      · simpa only [hend hs] using hend'
    · intro hs i hi hi'
      obtain ⟨α, ha⟩ := hlong hs i hi hi'
      exact ⟨α, by simpa only [hl hs i hi hi' α] using ha⟩
  · rintro ⟨hshort, hlong⟩
    constructor
    · intro hs
      obtain ⟨hedge, hend'⟩ := hshort hs
      constructor
      · intro i hi
        simpa only [he hs i hi] using hedge i hi
      · simpa only [hend hs] using hend'
    · intro hs i hi hi'
      obtain ⟨α, ha⟩ := hlong hs i hi hi'
      exact ⟨α, by simpa only [hl hs i hi hi' α] using ha⟩

end WeldedPath.VerifierBatch

end


-- Solutions.WeldedPathVerifierRealization
section

namespace WeldedPath

open QAlgorithms Supplement

theorem verifier_realization_proof (n l : ℕ) (G : WeldedInstance n)
    (W : Type) [Fintype W] [DecidableEq W] (q : ℕ) (hq : 1 ≤ q)
    (A : QueryAlg (Qubits (2 * n + 1) × Fin 3) (Qubits (2 * n + 1)) W q)
    (out : ((Qubits (2 * n + 1) × Fin 3) × Qubits (2 * n + 1)) × W →
      List (Fin 3 × Qubits (2 * n + 1))) :
    ∃ (W' : Type) (instF : Fintype W') (instD : DecidableEq W'),
      letI : Fintype W' := instF
      letI : DecidableEq W' := instD
      ∃ (B : QueryAlg (Qubits (2 * n + 1) × Fin 3) (Qubits (2 * n + 1)) W' (7 * q + 3))
        (acc : ((Qubits (2 * n + 1) × Fin 3) × Qubits (2 * n + 1)) × W' → Prop),
        ∀ S : Finset (Equiv.Perm (Label n) × Equiv.Perm G.edges),
          G.probOver l S B (fun _ => acc) =
            G.probOver l S A (fun σ z => Accepts39 l G σ q (out z)) := by
  classical
  obtain ⟨B, acc, hB⟩ := QueryBatchRealization.batch_realization
    (0 : Qubits (2 * n + 1) × Fin 3) A
    (fun z => VerifierBatch.addr q (out z))
    (fun z => VerifierBatch.test q hq (out z))
  refine ⟨QueryBatchRealization.Work (Qubits (2 * n + 1) × Fin 3)
    (Qubits (2 * n + 1)) W (6 * q + 3),
    instFintypeProd W (((Qubits (2 * n + 1) × Fin 3) × Qubits (2 * n + 1)) ×
      (Fin (6 * q + 3) → Qubits (2 * n + 1))),
    (fun a b => instDecidableEqProd a b), ?_⟩
  have hcount : q + (6 * q + 3) = 7 * q + 3 := by omega
  rw [← hcount]
  refine ⟨B, acc, ?_⟩
  intro S
  unfold WeldedInstance.probOver avgOver
  congr 1
  apply Finset.sum_congr rfl
  intro σ hσ
  refine (hB (G.oracleFn l σ)).trans ?_
  have hevent :
      (fun z => VerifierBatch.test q hq (out z)
        (fun j => G.oracleFn l σ (VerifierBatch.addr q (out z) j))) =
      (fun z => Accepts39 l G σ q (out z)) := by
    funext z
    exact propext (VerifierBatch.test_oracle_iff l G σ q hq (out z))
  simp only [hevent]

end WeldedPath

end

open WeldedPath QAlgorithms WeldedPath.Supplement

theorem solution (n l : ℕ) (G : WeldedInstance n)
    (W : Type) [Fintype W] [DecidableEq W] (q : ℕ) (hq : 1 ≤ q)
    (A : QueryAlg (Qubits (2 * n + 1) × Fin 3) (Qubits (2 * n + 1)) W q)
    (out : ((Qubits (2 * n + 1) × Fin 3) × Qubits (2 * n + 1)) × W →
      List (Fin 3 × Qubits (2 * n + 1))) :
    ∃ (W' : Type) (instF : Fintype W') (instD : DecidableEq W'),
      letI : Fintype W' := instF
      letI : DecidableEq W' := instD
      ∃ (B : QueryAlg (Qubits (2 * n + 1) × Fin 3) (Qubits (2 * n + 1)) W' (7 * q + 3))
        (acc : ((Qubits (2 * n + 1) × Fin 3) × Qubits (2 * n + 1)) × W' → Prop),
        ∀ S : Finset (Equiv.Perm (Label n) × Equiv.Perm G.edges),
          G.probOver l S B (fun _ => acc) =
            G.probOver l S A (fun σ z => Accepts39 l G σ q (out z)) := by
  exact WeldedPath.verifier_realization_proof n l G W q hq A out
