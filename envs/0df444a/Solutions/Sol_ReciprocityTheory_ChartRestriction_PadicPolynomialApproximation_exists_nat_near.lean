-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.PadicPolynomialApproximation.exists_nat_near
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:42:04.488893+00:00
-- url     : https://prove2.me/submissions/ac8688dc-790f-42c2-a689-2576fbf3964e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_TorDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_TchOfIntegral
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_NormEqOfNormSubLt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_TorRes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Classical
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.PadicPolynomialApproximation
open Polynomial Finset
variable (l : ℕ) [Fact l.Prime]
namespace ReciprocityTheory.ChartRestriction.PadicPolynomialApproximation
theorem _root_.solution (a : ℚ_[l]) (ha : ‖a‖ ≤ 1) : ∃ n : ℕ, ‖a - n‖ < 1 := by
  set x : ℤ_[l] := ⟨a, ha⟩ with hxdef
  obtain ⟨n, hn⟩ := PadicInt.denseRange_natCast.exists_dist_lt x one_pos
  have hxa : (x : ℚ_[l]) = a := rfl
  refine ⟨n, ?_⟩
  rw [dist_eq_norm, PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_natCast, hxa] at hn
  exact hn
end ReciprocityTheory.ChartRestriction.PadicPolynomialApproximation
