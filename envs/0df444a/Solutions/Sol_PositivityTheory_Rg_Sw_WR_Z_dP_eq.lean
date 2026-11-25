-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.Z.dP_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:20:42.019824+00:00
-- url     : https://prove2.me/submissions/e3e15d83-4486-47e4-b4da-df4d77adcc01

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainA
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_Z_det_one_add_sq

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
theorem _root_.solution (y : E n) : (1 + herm y * herm y).det = ((dP y : ℝ) : ℂ) := by
  unfold dP
  rw [det_one_add_sq 1 (Or.inl rfl) y, Complex.ofReal_re]
end PositivityTheory.Rg.Sw.WR.Z
