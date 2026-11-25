-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_HodgeDerivative_imTau_eq_eaf25bdf3e9f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:48:56.921918+00:00
-- url     : https://prove2.me/submissions/531a4460-541e-4bcd-816d-40c070b82933

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsBounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PChartBounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PHodgeDerivative
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_HodgeDerivative_logLift_mem_9850b514c279
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_HodgeDerivative_expCover_logLift_06dd0ae602f8

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Metric Filter Topology Matrix
open GroundTheory.Heights₂.Heights.MCBounds GroundTheory.Heights₂.Heights.MCDet
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.Regular.HodgeDerivative
namespace GroundTheory.Heights₂.Heights.Regular.HodgeDerivative
theorem _root_.solution {n a g : ℕ} (P : PeriodPolydisc n a g) {T0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ}
    (hT : P.IsTau0Ext T0) {z : Fin n → ℂ} (hz : z ∈ puncturedChart P.a_le (ball (0 : Fin n → ℂ) 1)) :
    P.imTau z = chartImag P.a_le T0 (fun i => (P.B i).map (Int.cast : ℤ → ℝ)) z := by
  have hw := logLift_mem P.a_le hz
  have h0 : P.tau0 (logLift a z) = T0 z := by
    rw [hT.2 _ hw, expCover_logLift P.a_le hz.2]
  have hτ : P.τ (logLift a z) = T0 z + ∑ i : Fin a,
      (logLift a z (Fin.castLE P.a_le i) / (2 * Real.pi * Complex.I)) •
        (P.B i).map (Int.cast : ℤ → ℂ) := by
    rw [← h0, PeriodPolydisc.tau0, sub_add_cancel]
  ext p q
  simp only [PeriodPolydisc.imTau, hτ, chartImag, map_apply, Matrix.add_apply, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, Complex.add_im, Complex.im_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi : (Fin.castLE P.a_le i).val < a := i.isLt
  simp only [logLift, if_pos hi, Complex.mul_im, Complex.intCast_re, Complex.intCast_im, mul_zero,
    zero_add, im_div_two_pi_I, Complex.log_re, cuspTime, cuspCoord, Real.log_inv]
  ring
end GroundTheory.Heights₂.Heights.Regular.HodgeDerivative
