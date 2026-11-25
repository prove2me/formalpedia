-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.Z.herm_star
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:53:35.104258+00:00
-- url     : https://prove2.me/submissions/dc8bd242-d72a-454a-8aec-97f19e368ba9

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainA
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_Z_herm_isHermitian

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
theorem _root_.solution (y : E n) (i j : Fin n) : star (herm y i j) = herm y j i := by
  simpa [conjTranspose_apply] using congrFun (congrFun (herm_isHermitian y).eq j) i
end PositivityTheory.Rg.Sw.WR.Z
