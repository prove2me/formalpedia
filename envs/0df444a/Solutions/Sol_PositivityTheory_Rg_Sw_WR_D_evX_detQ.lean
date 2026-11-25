-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.D.evX_detQ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:52:28.006316+00:00
-- url     : https://prove2.me/submissions/58a31376-c410-4326-bdc3-ebbe090838fb

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
theorem _root_.solution (ε : Fin m → Bool) (x : Fin m → Fin n → ℂ) : evX (detQ ε) x = (gramX ε x).det := by
  rw [evX, detQ, RingHom.map_det]
  rfl
end PositivityTheory.Rg.Sw.WR.D
