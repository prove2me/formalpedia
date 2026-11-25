-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.B.norm_det_uM_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:39:22.746626+00:00
-- url     : https://prove2.me/submissions/e33b1eae-a40d-4ee7-b9a0-f36d08f276a4

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundA
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_uM_eq
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_norm_det_Am_sq

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
theorem _root_.solution {s : ℂ} (hs : s = 1 ∨ s = -1) (y : E n) : ‖(uM s y).det‖ ^ 2 = (dP y)⁻¹ := by
  rw [uM_eq, det_nonsing_inv, Ring.inverse_eq_inv, norm_inv, inv_pow, norm_det_Am_sq hs]
end PositivityTheory.Rg.Sw.WR.B
