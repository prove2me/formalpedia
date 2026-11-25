-- Prove2me | solution 1 for P2M_PositivityTheory_Rg_Sw_WR_D_hinv_herm__6df79ca13e18
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:50:16.279882+00:00
-- url     : https://prove2.me/submissions/5d4bab65-2a1f-4547-b5ce-b04ef24474b3

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DensDefs
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ContinuousEvX

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D
open PositivityTheory.Rg.Sw
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.D
theorem _root_.solution (y : E n) : hinv (herm y) = y := by
  funext i j
  simp [hinv, herm]
  ring
end PositivityTheory.Rg.Sw.WR.D
