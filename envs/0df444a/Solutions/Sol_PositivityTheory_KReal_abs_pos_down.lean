-- Prove2me | solution 1 for PositivityTheory.KReal.abs_pos_down
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:34:09.221065+00:00
-- url     : https://prove2.me/submissions/538fc407-2426-406f-83b0-c62a611e9ef6

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreShape
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCasW
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreComb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace
open PositivityTheory PositivityTheory.KReal
namespace PositivityTheory.KReal
theorem _root_.solution {m : ℕ} (hm : 0 < m) : |(m : ℚ) - 1| - |(m : ℚ)| = -1 := by
  have h1 : (1 : ℚ) ≤ m := by exact_mod_cast hm
  rw [abs_of_nonneg (by linarith : (0 : ℚ) ≤ (m : ℚ) - 1), abs_of_nonneg (by linarith : (0 : ℚ) ≤ (m : ℚ))]
  ring
end PositivityTheory.KReal
