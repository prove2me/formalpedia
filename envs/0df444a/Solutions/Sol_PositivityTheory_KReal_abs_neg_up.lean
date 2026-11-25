-- Prove2me | solution 1 for PositivityTheory.KReal.abs_neg_up
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:36:32.723808+00:00
-- url     : https://prove2.me/submissions/c78c74ae-82b2-412e-b10a-27687ae789a5

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
theorem _root_.solution {m : ℕ} (hm : 0 < m) : |-(m : ℚ) + 1| - |-(m : ℚ)| = -1 := by
  have : (1 : ℚ) ≤ m := by exact_mod_cast hm
  rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
  ring
end PositivityTheory.KReal
