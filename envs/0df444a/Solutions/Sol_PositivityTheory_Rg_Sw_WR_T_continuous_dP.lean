-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.T.continuous_dP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:02:40.602244+00:00
-- url     : https://prove2.me/submissions/5b3ef49a-ed7f-44ec-9051-bb3e45b1d219

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DifferentiableOfTop
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ContinuousHerm
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_T_continuous_herm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Filter Topology
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.T
open PositivityTheory.Rg.Sw
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.T
theorem _root_.solution : Continuous (dP : E n → ℝ) := by
  unfold dP
  exact Complex.continuous_re.comp ((continuous_const.add (continuous_herm.matrix_mul continuous_herm)).matrix_det)
end PositivityTheory.Rg.Sw.WR.T
