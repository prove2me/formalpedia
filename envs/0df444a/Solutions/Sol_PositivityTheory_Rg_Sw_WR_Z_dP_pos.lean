-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.Z.dP_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:26:58.376269+00:00
-- url     : https://prove2.me/submissions/381fd82a-9c9c-43a0-8392-c66f7d341d83

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainA
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_Z_det_X_ne
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_Z_det_one_add_sq
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_Z_dP_eq

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
theorem _root_.solution (y : E n) : 0 < dP y := by
  have h := dP_eq y
  rw [det_one_add_sq 1 (Or.inl rfl) y] at h
  have h2 := congrArg Complex.re h
  simp only [Complex.ofReal_re] at h2
  rw [← h2]
  exact Complex.normSq_pos.2 (det_X_ne 1 (Or.inl rfl) y)
end PositivityTheory.Rg.Sw.WR.Z
