-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P23.projectionDifference_kernel
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T20:40:53.703815+00:00
-- url     : https://prove2.me/submissions/f1f9b01f-a4f1-4289-92e8-56fd8e06af22

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P23

open scoped BigOperators

theorem solution
    {K F : Type*} [RCLike K] [NormedAddCommGroup F] [InnerProductSpace K F] [CompleteSpace F]
    (V1 V2 : ClosedSubmodule K F) :
    (V1.toSubmodule ⊓ V2.toSubmodule) ⊔
        (V1.toSubmoduleᗮ ⊓ V2.toSubmoduleᗮ) =
      LinearMap.ker ((V1.toSubmodule.starProjection - V2.toSubmodule.starProjection).toLinearMap) := by
  apply le_antisymm
  · rw [sup_le_iff]
    constructor
    · intro x hx
      obtain ⟨h1, h2⟩ := Submodule.mem_inf.mp hx
      rw [LinearMap.mem_ker]
      show (V1.toSubmodule.starProjection - V2.toSubmodule.starProjection) x = 0
      rw [ContinuousLinearMap.sub_apply,
        Submodule.starProjection_eq_self_iff (K := V1.toSubmodule) |>.mpr h1,
        Submodule.starProjection_eq_self_iff (K := V2.toSubmodule) |>.mpr h2, sub_self]
    · intro x hx
      obtain ⟨h1, h2⟩ := Submodule.mem_inf.mp hx
      rw [LinearMap.mem_ker]
      show (V1.toSubmodule.starProjection - V2.toSubmodule.starProjection) x = 0
      rw [ContinuousLinearMap.sub_apply,
        Submodule.starProjection_apply_eq_zero_iff (K := V1.toSubmodule) |>.mpr h1,
        Submodule.starProjection_apply_eq_zero_iff (K := V2.toSubmodule) |>.mpr h2, sub_self]
  · intro x hx
    rw [LinearMap.mem_ker] at hx
    have hx0 : (V1.toSubmodule.starProjection - V2.toSubmodule.starProjection) x = 0 := hx
    rw [ContinuousLinearMap.sub_apply, sub_eq_zero] at hx0
    have hdec : V1.toSubmodule.starProjection x + (x - V1.toSubmodule.starProjection x) = x :=
      add_sub_cancel _ _
    rw [← hdec]
    apply Submodule.add_mem_sup
    · refine Submodule.mem_inf.mpr ⟨Submodule.starProjection_apply_mem _ x, ?_⟩
      rw [hx0]
      exact Submodule.starProjection_apply_mem _ x
    · refine Submodule.mem_inf.mpr
        ⟨Submodule.sub_starProjection_mem_orthogonal (K := V1.toSubmodule) x, ?_⟩
      rw [hx0]
      exact Submodule.sub_starProjection_mem_orthogonal (K := V2.toSubmodule) x
