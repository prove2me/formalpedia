-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.B.cls_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:58:47.107714+00:00
-- url     : https://prove2.me/submissions/fb8cca26-41a3-4b7d-8f4f-337cab30748c

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBound
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_evUV_eq
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_norm_eval_le
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_norm_ent_le
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_dP_pos
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_norm_det_pow
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_norm_det_uM_sq
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_norm_det_vM_sq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.B
open PositivityTheory.Rg.Sw
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.B
theorem _root_.solution {s : ℂ} (hs : s = 1 ∨ s = -1) (z : ℂ) (p q : ℕ) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ)
    (y : E n) : ‖cls s z p q R y‖ ≤
      (∑ m ∈ R.support, ‖MvPolynomial.coeff m R‖) * (dP y) ^ (-(z.re + (p + q : ℝ) / 2)) := by
  have hd := dP_pos y
  have e1 : ‖((dP y : ℝ) : ℂ) ^ (-z)‖ = (dP y) ^ (-z.re) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hd, Complex.neg_re]
  have e2 := norm_det_pow hd (norm_det_uM_sq hs y) p
  have e3 := norm_det_pow hd (norm_det_vM_sq hs y) q
  have e4 := norm_eval_le (fun e => ent s e y) (norm_ent_le hs y) R
  simp only [cls, norm_mul]
  rw [e1, e2, e3]
  have hC : 0 ≤ ∑ m ∈ R.support, ‖MvPolynomial.coeff m R‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hpos : 0 ≤ (dP y) ^ (-z.re) * (dP y) ^ (-(p : ℝ) / 2) * (dP y) ^ (-(q : ℝ) / 2) := by positivity
  calc (dP y) ^ (-z.re) * (dP y) ^ (-(p : ℝ) / 2) * (dP y) ^ (-(q : ℝ) / 2) * ‖evUV s R y‖
      ≤ (dP y) ^ (-z.re) * (dP y) ^ (-(p : ℝ) / 2) * (dP y) ^ (-(q : ℝ) / 2) *
          (∑ m ∈ R.support, ‖MvPolynomial.coeff m R‖) := mul_le_mul_of_nonneg_left (by rw [evUV_eq]; exact e4) hpos
    _ = _ := by
      rw [← Real.rpow_add hd, ← Real.rpow_add hd]
      rw [mul_comm]; congr 2; ring
end PositivityTheory.Rg.Sw.WR.B
