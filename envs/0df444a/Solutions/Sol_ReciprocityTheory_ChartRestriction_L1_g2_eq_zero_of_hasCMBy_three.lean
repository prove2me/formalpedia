-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.g2_eq_zero_of_hasCMBy_three
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:00:00.047415+00:00
-- url     : https://prove2.me/submissions/354eb484-3a50-4664-9205-f54369d54a8b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_G2EqZeroOfHasCMByThree
import Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_key


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (L : PeriodPair) (hCM : HasCMBy 3 L) : L.g₂ = 0 := by
  have hsq := omegaK_three_sq
  have h4 : omegaK 3 ^ 4 = -omegaK 3 := by
    linear_combination (omegaK 3 ^ 2 + omegaK 3) * hsq
  have h0 : omegaK 3 ≠ 0 := by
    intro h
    rw [h] at hsq
    norm_num at hsq
  have h1 : omegaK 3 ≠ -1 := by
    intro h
    rw [h] at hsq
    norm_num at hsq
  have key : L.G 4 = (omegaK 3 ^ 4)⁻¹ * L.G 4 := by
    conv_lhs => rw [PeriodPair.G, ← (mulOmegaEquiv L hCM).tsum_eq]
    rw [PeriodPair.G, ← tsum_mul_left]
    refine tsum_congr fun l => ?_
    show ((omegaK 3 * (l : ℂ)) ^ 4)⁻¹ = _
    rw [mul_pow, mul_inv]
  have hG : L.G 4 = 0 := by
    have h40 : omegaK 3 ^ 4 ≠ 0 := pow_ne_zero _ h0
    have h2 : omegaK 3 ^ 4 * L.G 4 = L.G 4 := by
      conv_lhs => rw [key]
      rw [mul_inv_cancel_left₀ h40]
    rw [h4] at h2
    have h3 : (omegaK 3 + 1) * L.G 4 = 0 := by linear_combination -h2
    rcases mul_eq_zero.mp h3 with h | h
    · exact absurd (by linear_combination h) h1
    · exact h
  rw [PeriodPair.g₂, hG, mul_zero]
end ReciprocityTheory.ChartRestriction.L1
