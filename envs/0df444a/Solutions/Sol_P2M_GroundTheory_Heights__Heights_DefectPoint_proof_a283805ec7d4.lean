-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DefectPoint_proof_a283805ec7d4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:55:23.674883+00:00
-- url     : https://prove2.me/submissions/803ed290-670e-48db-bc42-d83cc369e8a0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLogBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PDefectPoint
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isMultiHomog_pointForm_67f7417897ff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermNorm_dualNorm_pos_3da77c812dcb


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Matrix
noncomputable section
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights
namespace DefectPoint
theorem _root_.solution (h1 : PointLine.Statement) (h2 : PointChowForm.Statement)
    (h3 : ConeIntegralLine.Statement) (h4 : FsLogSmul.Statement) (h5 : ConeIntegralMass.Statement) :
    DefectPoint.Statement := by
  intro n h W g hW hg
  obtain ⟨y, hy0, hline, hmem⟩ := h1 n W g hW hg
  obtain ⟨c, hc, hgeq⟩ := h2 n W g y hg hy0 hline
  have hmass : coneIntegral h W 0 (fun _ => 1) = 1 := by
    have := h5 n 0 1 h W g hW hg (hgeq ▸ isMultiHomog_pointForm c y)
    simpa using this
  have hd : 0 < h.dualNorm y := h.dualNorm_pos hy0
  refine ⟨Real.log ‖c‖ + Real.log (h.dualNorm y), fun u hu => ?_⟩
  have hpair : ∑ j, u j * y j ≠ 0 := by
    intro h0
    apply hu
    rw [hmem]
    intro t
    simp only [linForm, map_sum, map_mul, eval_C, eval_X, Pi.smul_apply, smul_eq_mul]
    calc ∑ j, u j * (t * y j) = t * ∑ j, u j * y j := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
      _ = 0 := by rw [h0, mul_zero]
  have hev : eval (fun ij => u ij.2) g = c * ∑ j, u j * y j := by
    rw [hgeq]
    simp only [map_mul, map_sum, eval_C, eval_X]
    congr 1
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hcone : coneIntegral h W 0 (fsLog h u) = fsLog h u y := by
    rw [h3 n h W y hline (fsLog h u) (fun t ht => h4 n h u y t ht), hmass, mul_one]
  refine ⟨by rw [hev]; exact mul_ne_zero hc hpair, ?_⟩
  rw [hev, hcone, fsLog, norm_mul,
    Real.log_mul (norm_ne_zero_iff.mpr hc) (norm_ne_zero_iff.mpr hpair),
    Real.log_div (norm_ne_zero_iff.mpr hpair) hd.ne']
  ring
end DefectPoint
end GroundTheory.Heights₂.Heights
