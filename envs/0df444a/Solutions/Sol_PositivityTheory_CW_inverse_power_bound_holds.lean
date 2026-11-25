-- Prove2me | solution 1 for PositivityTheory.CW.inverse_power_bound_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:38:12.872426+00:00
-- url     : https://prove2.me/submissions/98d7a608-2357-42ba-8182-5fa4f4231ffd

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_InversePowerBoundHolds
import Theorems.Thm_PositivityTheory_CW_InversePowerBound_sq_le_inv_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
open PositivityTheory PositivityTheory.CW
namespace PositivityTheory.CW
theorem _root_.solution : A10 := by
  intro s _hs
  refine ⟨(s : ℝ) ^ 4 / 16, by positivity, fun y hy => ?_⟩
  have hpos : 0 < ((1 + y) ^ s)⁻¹ := inv_pos.mpr (pow_pos (by linarith) s)

  have hsq : 1 - (s : ℝ) * y + (s : ℝ) ^ 2 / 4 * y ^ 2 = (1 - (s : ℝ) * y / 2) ^ 2 := by ring
  have e : (s : ℝ) ^ 4 / 16 * y ^ 4 = ((s : ℝ) * y / 2) ^ 4 := by ring
  by_cases h0 : 0 ≤ 1 - (s : ℝ) * y / 2
  · have h := InversePowerBound.sq_le_inv_pow s y hy h0
    have : 0 ≤ (s : ℝ) ^ 4 / 16 * y ^ 4 := by positivity
    linarith
  ·
    rw [not_le] at h0
    have hu : 1 < (s : ℝ) * y / 2 := by linarith
    have k1 : (1 - (s : ℝ) * y / 2) ^ 2 ≤ ((s : ℝ) * y / 2) ^ 2 := by nlinarith
    have k2 : ((s : ℝ) * y / 2) ^ 2 ≤ ((s : ℝ) * y / 2) ^ 4 := by
      have : 1 ≤ ((s : ℝ) * y / 2) ^ 2 := by nlinarith
      nlinarith
    linarith
end PositivityTheory.CW
