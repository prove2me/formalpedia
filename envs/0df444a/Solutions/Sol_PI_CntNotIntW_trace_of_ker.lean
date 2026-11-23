-- Prove2me | solution 1 for PI.CntNotIntW.trace_of_ker
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:16:59.193099+00:00
-- url     : https://prove2.me/submissions/b0420979-9995-4ab8-820e-4efd0d6b4e9b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CountNonIntegrality_TraceOfKer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.CntNotIntW
open scoped TensorProduct
namespace PI.CntNotIntW
theorem _root_.solution {Q A B : Type*} [Field Q] [CommRing A] [Algebra Q A] [FiniteDimensional Q A]
    [Field B] [Algebra Q B] [FiniteDimensional Q B] (π : A →ₐ[Q] B) (hπ : Function.Surjective π)
    (a : A) (ha : ∀ x, π x = 0 → a * x = 0) : Algebra.trace Q A a = Algebra.trace Q B (π a) := by
  classical
  obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective π.toLinearMap
    (LinearMap.range_eq_top.mpr hπ)
  have hsy : ∀ y, π (s y) = y := fun y => LinearMap.congr_fun hs y

  have hL : Algebra.lmul Q A a = (Algebra.lmul Q A a ∘ₗ s) ∘ₗ π.toLinearMap := by
    ext x
    have hk : π (x - s (π x)) = 0 := by rw [map_sub, hsy, sub_self]
    have h := ha _ hk
    rw [mul_sub, sub_eq_zero] at h
    simpa using h
  rw [Algebra.trace_apply, Algebra.trace_apply, hL, LinearMap.trace_comp_comm']
  congr 1
  ext y
  simp [hsy]
end PI.CntNotIntW
