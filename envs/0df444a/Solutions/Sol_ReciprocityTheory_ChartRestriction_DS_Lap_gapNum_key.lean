-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.gapNum_key
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:12:55.953871+00:00
-- url     : https://prove2.me/submissions/008e67cb-3216-47ea-99bc-c1e185b5cf68

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_SpectralGap_GapNum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap
namespace ReciprocityTheory.ChartRestriction.DS.Lap
theorem _root_.solution (Q Nn T : ℝ) (hQ : 1 ≤ Q) (hN : 2 ≤ Nn) (hT : Nn + 5 ≤ T) :
    160 * Q ^ 2 * Nn ^ 2 ≤ 2 * (Nn + 2 * Q * T) ^ 3 := by
  have hQ0 : 0 ≤ Q := by linarith
  have hN0 : 0 ≤ Nn := by linarith
  have hT0 : 0 ≤ T := by linarith
  have h1 : (2 * Q * T) ^ 3 ≤ (Nn + 2 * Q * T) ^ 3 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 3
  have h2 : 17 * Nn ^ 2 ≤ T ^ 3 := by
    have : (Nn + 5) ^ 3 ≤ T ^ 3 := pow_le_pow_left₀ (by linarith) hT 3
    nlinarith [sq_nonneg Nn]
  have h3 : Q ^ 2 ≤ Q ^ 3 := by nlinarith [sq_nonneg Q]
  have h4 : 16 * Q ^ 2 * (17 * Nn ^ 2) ≤ 16 * Q ^ 3 * T ^ 3 := by
    have := mul_le_mul h3 h2 (by positivity) (by positivity)
    nlinarith
  nlinarith [sq_nonneg Q, sq_nonneg Nn]
end ReciprocityTheory.ChartRestriction.DS.Lap
