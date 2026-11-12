-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P67.universalForm_universal
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T20:28:55.895002+00:00
-- url     : https://prove2.me/submissions/a82f04a1-a77a-466a-9b80-804e188fe830

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P67

open scoped TensorProduct

universe u v w

attribute [local instance] QAlgorithms.Papers.Independent.Intakenext100.P67.dependentLieRing

attribute [local instance] QAlgorithms.Papers.Independent.Intakenext100.P67.dependentLieAlgebra

section UniversalForm

variable (L : Type u) [LieRing L] [LieAlgebra ℝ L]

open QAlgorithms.Papers.Independent.Intakenext100.P67 in
theorem solution [FiniteDimensional ℝ L]
    (W : Type v) [AddCommGroup W] [Module ℝ W] :
    InvariantSymmetric L (universalForm L) ∧
      ∀ B : L →ₗ[ℝ] L →ₗ[ℝ] W, InvariantSymmetric L B →
        ∃! q : UniversalFormSpace L →ₗ[ℝ] W,
          ∀ x y : L, q (universalForm L x y) = B x y := by
  have hform : ∀ x y : L, universalForm L x y = (universalRelations L).mkQ (x ⊗ₜ[ℝ] y) :=
    fun x y => rfl
  refine ⟨⟨fun x y => ?_, fun x y z => ?_⟩, fun B hB => ?_⟩
  · rw [hform, hform, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    exact Submodule.subset_span (Or.inl ⟨x, y, rfl⟩)
  · rw [hform, hform, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    have h : ⁅y, x⁆ ⊗ₜ[ℝ] z + x ⊗ₜ[ℝ] ⁅y, z⁆ ∈ universalRelations L :=
      Submodule.subset_span (Or.inr ⟨y, x, z, rfl⟩)
    have e : ⁅x, y⁆ ⊗ₜ[ℝ] z - x ⊗ₜ[ℝ] ⁅y, z⁆ = -(⁅y, x⁆ ⊗ₜ[ℝ] z + x ⊗ₜ[ℝ] ⁅y, z⁆) := by
      rw [← lie_skew x y, TensorProduct.neg_tmul]
      abel
    rw [e]
    exact (universalRelations L).neg_mem h
  · have hle : universalRelations L ≤ LinearMap.ker (TensorProduct.lift B) := by
      unfold universalRelations
      rw [Submodule.span_le]
      rintro t (⟨x, y, rfl⟩ | ⟨x, y, z, rfl⟩)
      · simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, TensorProduct.lift.tmul]
        rw [hB.1 x y, sub_self]
      · simp only [SetLike.mem_coe, LinearMap.mem_ker, map_add, TensorProduct.lift.tmul]
        rw [← hB.2 y x z, ← lie_skew y x, map_neg, LinearMap.neg_apply, add_neg_cancel]
    refine ⟨(universalRelations L).liftQ (TensorProduct.lift B) hle, fun x y => ?_, ?_⟩
    · rw [hform, Submodule.mkQ_apply, Submodule.liftQ_apply, TensorProduct.lift.tmul]
    · intro q' hq'
      apply Submodule.linearMap_qext
      apply TensorProduct.ext'
      intro x y
      simp only [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.liftQ_apply,
        TensorProduct.lift.tmul]
      rw [← Submodule.mkQ_apply, ← hform, hq' x y]

end UniversalForm
