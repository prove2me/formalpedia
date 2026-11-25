-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.Z.det_Y_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:18:42.007996+00:00
-- url     : https://prove2.me/submissions/98bf7c02-9c52-457e-a5fb-44413ec86a9f

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainA
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_Z_conjT_X
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_Z_det_X_ne

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
theorem _root_.solution (s : ℂ) (hs : s = 1 ∨ s = -1) (y : E n) : (1 + (Complex.I * s) • herm y).det ≠ 0 := by
  rw [← conjT_X s hs y, det_conjTranspose]
  exact (star_ne_zero).2 (det_X_ne s hs y)
end PositivityTheory.Rg.Sw.WR.Z
