-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.I.continuous_herm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:50:18.3268+00:00
-- url     : https://prove2.me/submissions/ead4e8ac-c2ed-4b64-8f7a-53e20d66fdb1

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_Integr

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
theorem _root_.solution : Continuous (herm : E n → Matrix (Fin n) (Fin n) ℂ) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  unfold herm
  fun_prop
end PositivityTheory.Rg.Sw.WR.I
