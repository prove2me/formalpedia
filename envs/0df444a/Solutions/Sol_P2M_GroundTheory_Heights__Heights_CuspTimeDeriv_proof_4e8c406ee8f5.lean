-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CuspTimeDeriv_proof_4e8c406ee8f5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:55:43.64018+00:00
-- url     : https://prove2.me/submissions/3b912cec-03d0-4527-874e-c53bea2ada5f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsBounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PCuspTimeDeriv
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCCuspTimeDeriv_lipschitz_norm_coord_6e11104b48f3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCCuspTimeDeriv_inv_le_exp_half_log_8bddef3919ec
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_cusp_norm_lt_b55c72d768a7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_log_inv_sq_nonneg_b1faa07e0605


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
open MCCuspTimeDeriv
namespace GroundTheory.Heights₂.Heights
namespace CuspTimeDeriv
theorem _root_.solution : CuspTimeDeriv.Statement := by
  intro D z hz i
  set c : Fin D.n := Fin.castLE D.a_le i with hc
  have hz0 : z c ≠ 0 := hz.2 i
  have hlt : ‖z c‖ < 1 := MCBounds.cusp_norm_lt D hz.1 i
  have hpos : 0 < ‖z c‖ := norm_pos_iff.mpr hz0

  let N : (Fin D.n → ℂ) → ℝ := fun w => ‖w c‖
  let φ : ℝ → ℝ := fun y => (2 * Real.pi)⁻¹ * -Real.log y
  have hfun : (fun w => cuspTime D.a_le w i) = φ ∘ N := by
    funext w
    simp only [cuspTime, cuspCoord, φ, N, Function.comp, Real.log_inv, hc]
  have hNd : DifferentiableAt ℝ N z :=
    DifferentiableAt.norm ℂ (differentiableAt_apply (𝕜 := ℝ) c z) hz0
  have hφ : HasDerivAt φ ((2 * Real.pi)⁻¹ * -(‖z c‖)⁻¹) (N z) :=
    ((Real.hasDerivAt_log hpos.ne').neg).const_mul _
  have hcomp : HasFDerivAt (φ ∘ N) (((2 * Real.pi)⁻¹ * -(‖z c‖)⁻¹) • fderiv ℝ N z) z :=
    hφ.comp_hasFDerivAt z hNd.hasFDerivAt
  rw [hfun]
  refine ⟨hcomp.differentiableAt, ?_⟩
  rw [hcomp.fderiv, norm_smul]
  have hNle : ‖fderiv ℝ N z‖ ≤ 1 := by
    have := norm_fderiv_le_of_lipschitz ℝ (x₀ := z) (lipschitz_norm_coord c)
    simpa using this
  have hpi : (2 * Real.pi)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [Real.pi_gt_three])
  have hpi0 : 0 ≤ (2 * Real.pi)⁻¹ := by positivity
  have hcoef : ‖(2 * Real.pi)⁻¹ * -(‖z c‖)⁻¹‖ ≤ (‖z c‖)⁻¹ := by
    rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg hpi0, abs_of_pos (inv_pos.mpr hpos)]
    exact mul_le_of_le_one_left (inv_pos.mpr hpos).le hpi

  have hterm : Real.log (‖z c‖ ^ 2)⁻¹ ≤ D.radius z := by
    have hsum : Real.log (‖cuspCoord D.a_le z i‖ ^ 2)⁻¹ ≤
        ∑ j, Real.log (‖cuspCoord D.a_le z j‖ ^ 2)⁻¹ :=
      Finset.single_le_sum (f := fun j => Real.log (‖cuspCoord D.a_le z j‖ ^ 2)⁻¹)
        (fun j _ => MCBounds.log_inv_sq_nonneg (MCBounds.cusp_norm_lt D hz.1 j)) (Finset.mem_univ i)
    have he := Real.exp_pos 1
    show Real.log (‖cuspCoord D.a_le z i‖ ^ 2)⁻¹ ≤ _
    simp only [PeriodChartData.radius, chartRadius]
    linarith
  have hexp : (‖z c‖)⁻¹ ≤ Real.exp (D.radius z / 2) :=
    (inv_le_exp_half_log hpos).trans (Real.exp_le_exp.mpr (by linarith))
  calc ‖(2 * Real.pi)⁻¹ * -(‖z c‖)⁻¹‖ * ‖fderiv ℝ N z‖ ≤ (‖z c‖)⁻¹ * 1 :=
        mul_le_mul hcoef hNle (norm_nonneg _) (inv_pos.mpr hpos).le
    _ ≤ Real.exp (D.radius z / 2) := by rw [mul_one]; exact hexp
end CuspTimeDeriv
end GroundTheory.Heights₂.Heights
