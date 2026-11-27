-- Prove2me | solution 1 for P2M_GlobalTheory_T_laurent_coeff_neg_eq_zero_of_bounded__b623b15fefff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:53:08.0663+00:00
-- url     : https://prove2.me/submissions/4c7c9001-c445-4eb0-866d-fefe6a053847

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LaurentCoeffNegEqZeroOfBounded
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LaurentCoeffNegEqZeroOfBoundedStatement
import Theorems.Thm_GlobalTheory_laurent_coeff_neg_eq_zero_of_bounded


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped LaurentSeries
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : ℂ⸨X⸩) (T C : ℝ), (∀ w : ℂ, T < w.im → ∃ x : ℂ, HasSum (fun m : ℤ => F.coeff m * eTwoPi w ^ m) x ∧ ‖x‖ ≤ C) → ∀ m : ℤ, m < 0 → F.coeff m = 0 := by
  first | exact @GlobalTheory.laurent_coeff_neg_eq_zero_of_bounded | exact GlobalTheory.laurent_coeff_neg_eq_zero_of_bounded | (intros; apply GlobalTheory.laurent_coeff_neg_eq_zero_of_bounded <;> assumption)
end _root_.GlobalTheory.T
