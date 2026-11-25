-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.Z.chain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:24:12.616383+00:00
-- url     : https://prove2.me/submissions/562abb22-3a27-489c-816f-ff68b11c530a

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainA
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_Z_delta_comp
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_Z_an_cay

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Z
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.Z
theorem _root_.solution : Chain := by
  intro n U F hU hherm hF N
  induction N generalizing F with
  | zero => intro y; rfl
  | succ N ih =>
    intro y
    rw [Function.iterate_succ_apply, delta_comp U hU hherm F hF, ih (cay F) (an_cay U hU F hF) y,
      ← Function.iterate_succ_apply]
end PositivityTheory.Rg.Sw.WR.Z
