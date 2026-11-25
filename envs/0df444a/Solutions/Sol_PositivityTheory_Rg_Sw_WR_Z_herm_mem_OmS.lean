-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.Z.herm_mem_OmS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:37:37.456806+00:00
-- url     : https://prove2.me/submissions/b9a203f9-5ea7-42eb-81de-10674d60959a

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainA
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_Z_det_X_ne
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_Z_det_Y_ne
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_Z_dP_eq
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_Z_dP_pos

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
theorem _root_.solution (s : ℂ) (hs : s = 1 ∨ s = -1) (y : E n) : (herm y : MC n) ∈ OmS s := by
  refine ⟨det_X_ne s hs y, det_Y_ne s hs y, ?_⟩
  show (1 + herm y * herm y).det ∈ Complex.slitPlane
  rw [dP_eq]
  exact Complex.ofReal_mem_slitPlane.2 (dP_pos y)
end PositivityTheory.Rg.Sw.WR.Z
