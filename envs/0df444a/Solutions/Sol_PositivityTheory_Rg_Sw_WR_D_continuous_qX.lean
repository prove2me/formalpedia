-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.D.continuous_qX
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:58:30.773097+00:00
-- url     : https://prove2.me/submissions/0c9e28f9-880a-4e87-9bec-3f749a0792fd

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DensDefs
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ContinuousEvX
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_continuous_evX

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
theorem _root_.solution (ε : Fin m → Bool) : Continuous (qX (n := n) ε) := by
  unfold qX hinv gramX
  exact continuous_pi fun i => continuous_pi fun j =>
    (Complex.continuous_re.comp (continuous_evX _)).add (Complex.continuous_im.comp (continuous_evX _))
end PositivityTheory.Rg.Sw.WR.D
