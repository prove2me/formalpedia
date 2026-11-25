-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.B.dirC_vM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:51:51.57841+00:00
-- url     : https://prove2.me/submissions/41ce6df9-1374-491a-bfa4-d5b7957d9680

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundB
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_entry_mul_single_mul
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_dirC_inv_entry
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_contDiff_Bm_entry
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_dirC_Bm_entry
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_det_Bm_ne
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_vM_eq


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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.B
open PositivityTheory.Rg.Sw
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.B
theorem _root_.solution {s : ℂ} (hs : s = 1 ∨ s = -1) (y : E n) (a b k l : Fin n) :
    dirC (fun y => vM s y a b) (vkl k l) y = -(Complex.I * s * (vM s y a l * vM s y k b)) := by
  rw [show (fun y => vM s y a b) = fun y => (Bm s y)⁻¹ a b from rfl,
    dirC_inv_entry (contDiff_Bm_entry s) (det_Bm_ne hs) (vkl k l) y ((Complex.I * s) • Matrix.single l k (1 : ℂ))
      (fun a b => by rw [dirC_Bm_entry, Matrix.smul_apply, smul_eq_mul]) a b]
  rw [← vM_eq, Matrix.neg_apply, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply,
    entry_mul_single_mul, smul_eq_mul]
end PositivityTheory.Rg.Sw.WR.B
