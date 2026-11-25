-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.B.norm_det_Am_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:32:51.26016+00:00
-- url     : https://prove2.me/submissions/27d2cf26-8568-4a39-a75d-f41966f8a377

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundA
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_Am_conjTranspose
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_det_Bm_mul_det_Am

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
theorem _root_.solution {s : ℂ} (hs : s = 1 ∨ s = -1) (y : E n) : ‖(Am s y).det‖ ^ 2 = dP y := by
  have h := det_Bm_mul_det_Am hs y
  rw [← Am_conjTranspose hs, det_conjTranspose] at h
  have h2 : star (Am s y).det * (Am s y).det = ((‖(Am s y).det‖ : ℂ)) ^ 2 := Complex.conj_mul' _
  rw [h2] at h
  exact_mod_cast h
end PositivityTheory.Rg.Sw.WR.B
