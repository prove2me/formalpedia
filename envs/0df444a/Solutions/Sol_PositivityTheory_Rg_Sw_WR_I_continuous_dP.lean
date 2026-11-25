-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.I.continuous_dP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:57:18.445562+00:00
-- url     : https://prove2.me/submissions/293a68d9-d36c-4ebd-960c-b3e209ed7008

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_Integr
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_I_continuous_herm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.I
open PositivityTheory.Rg.Sw
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.I
theorem _root_.solution : Continuous (dP : E n → ℝ) := by
  unfold dP
  have : Continuous fun y : E n => 1 + herm y * herm y := continuous_const.add (continuous_herm.matrix_mul continuous_herm)
  exact Complex.continuous_re.comp this.matrix_det
end PositivityTheory.Rg.Sw.WR.I
