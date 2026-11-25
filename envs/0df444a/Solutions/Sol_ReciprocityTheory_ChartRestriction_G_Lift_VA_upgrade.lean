-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Lift.VA.upgrade
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:16:58.446856+00:00
-- url     : https://prove2.me/submissions/9a7bedeb-e035-4f9a-8218-be4c019fb295

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ValuationLifting_LiftSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ValuationLifting_ValuationApproximation_LargeSmall
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ValuationLifting_ValuationApproximation_RhoProjectionAssembly
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Lift_VA_disc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Lift ReciprocityTheory.ChartRestriction.G.Lift.VA
open WithZero
variable {Ω : Type} [Field Ω]
namespace ReciprocityTheory.ChartRestriction.G.Lift.VA
theorem _root_.solution (v w : Valuation Ω (WithZero (Multiplicative ℤ))) (π : Ω) (hπ : v π = exp (1 : ℤ))
    (u : Ω) (hu : 1 ≤ v u) (hu' : w u < 1) : ∃ x, 1 < v x ∧ w x < 1 := by
  obtain ⟨m, -, hm⟩ := disc (w π) 1 one_ne_zero
  refine ⟨u ^ m * π, ?_, ?_⟩
  · rw [map_mul, map_pow, hπ]
    exact lt_of_lt_of_le (by rw [← exp_zero, exp_lt_exp]; norm_num)
      (le_mul_of_one_le_left' (one_le_pow_of_one_le' hu m))
  · rw [map_mul, map_pow]
    exact hm m le_rfl _ _ hu' le_rfl
end ReciprocityTheory.ChartRestriction.G.Lift.VA
