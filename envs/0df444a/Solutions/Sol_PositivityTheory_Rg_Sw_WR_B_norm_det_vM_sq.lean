-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.B.norm_det_vM_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:39:25.145889+00:00
-- url     : https://prove2.me/submissions/8ca660c9-7c36-4b8b-8084-e0ff5942e9ef

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundA
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_vM_eq
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_norm_det_Bm_sq

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
open scoped ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.B
open PositivityTheory.Rg.Sw
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.B
theorem _root_.solution {s : ℂ} (hs : s = 1 ∨ s = -1) (y : E n) : ‖(vM s y).det‖ ^ 2 = (dP y)⁻¹ := by
  rw [vM_eq, det_nonsing_inv, Ring.inverse_eq_inv, norm_inv, inv_pow, norm_det_Bm_sq hs]
end PositivityTheory.Rg.Sw.WR.B
