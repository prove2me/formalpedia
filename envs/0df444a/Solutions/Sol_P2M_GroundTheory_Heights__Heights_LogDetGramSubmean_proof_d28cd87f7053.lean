-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LogDetGramSubmean_proof_d28cd87f7053
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:03:30.616939+00:00
-- url     : https://prove2.me/submissions/c09f3d5c-6989-44f7-87fa-cd68d52bc65f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsPsh
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_DetIneq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PshCore
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PshMatrix
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PLogDetGramSubmean
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCDet_log_re_det_le_6dd05a54f808
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCDet_norm_det_mul_sq_le_of_posDef_b8853d9e2e1b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCDet_re_det_pos_df6c7fe9c329
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCPsh_analyticOnNhd_det_c705e943e556
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCPsh_cx_inv_7b358c22ed20
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCPsh_cx_mul_14a24d1b571e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCPsh_cx_one_40e68e603bc0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCPsh_cx_posDef_f752d4d37fd2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCPsh_exists_factor_19d70d2d1f7a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCPsh_le_circleAverage_of_minorant_4e512974bc58
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCPsh_mulVec_injective_of_rank_78b168dcc192
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCPsh_re_trace_eq_c0fe8cc86955


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
open Matrix Metric Real MCPsh
open scoped MatrixOrder ComplexOrder
noncomputable section
set_option maxHeartbeats 400000
namespace GroundTheory.Heights₂.Heights
namespace LogDetGramSubmean
theorem _root_.solution (hcont : LogDetGramContinuous.Statement) :
    LogDetGramSubmean.Statement := by
  classical
  intro g rk Y F hYpd hYc hYmean hF hFrank
  have h0mem : (0:ℂ) ∈ closedBall (0:ℂ) 1 := mem_closedBall_self zero_le_one
  have hsph : sphere (0:ℂ) 1 ⊆ closedBall 0 1 := sphere_subset_closedBall
  have hYu : ∀ ζ ∈ closedBall (0:ℂ) 1, IsUnit (Y ζ).det := fun ζ hζ =>
    (Matrix.isUnit_iff_isUnit_det _).mp (hYpd ζ hζ).isUnit
  have hFr : ∀ ζ ∈ closedBall (0:ℂ) 1, Function.Injective (F ζ).mulVec := fun ζ hζ =>
    mulVec_injective_of_rank (by rw [hFrank ζ hζ, Fintype.card_fin])
  have hFc : ContinuousOn F (closedBall 0 1) :=
    continuousOn_pi.mpr fun j => continuousOn_pi.mpr fun k => (hF j k).continuousOn
  have hφc : ContinuousOn (fun ζ => logDetGram (Y ζ) (F ζ)) (closedBall 0 1) :=
    hcont ℂ (closedBall 0 1) g rk Y F hYc hFc hYpd hFrank
  have hφint : CircleIntegrable (fun ζ => logDetGram (Y ζ) (F ζ)) 0 1 :=
    (hφc.mono hsph).circleIntegrable zero_le_one
  refine ⟨hφint, ?_⟩

  have hGpd : ∀ ζ ∈ closedBall (0:ℂ) 1,
      ((F ζ)ᴴ * ((Y ζ)⁻¹).map (fun x : ℝ => (x : ℂ)) * F ζ).PosDef := by
    intro ζ hζ
    have h := (cx_posDef (hYpd ζ hζ)).inv.conjTranspose_mul_mul_same (hFr ζ hζ)
    rw [cx_inv (hYu ζ hζ)] at h
    exact h
  have hGdet : ∀ ζ ∈ closedBall (0:ℂ) 1,
      0 < ((F ζ)ᴴ * ((Y ζ)⁻¹).map (fun x : ℝ => (x : ℂ)) * F ζ).det.re := by
    intro ζ hζ
    have h := MCDet.re_det_pos (hGpd ζ hζ)
    rw [RCLike.re_to_complex] at h
    exact h

  obtain ⟨B, hBu, hB⟩ := exists_factor (hGpd 0 h0mem)
  set Ci : Matrix (Fin g) (Fin g) ℂ := ((Y 0)⁻¹).map (fun x : ℝ => (x : ℂ)) with hCidef
  set W0 : Matrix (Fin g) (Fin rk) ℂ := Ci * F 0 * B⁻¹ with hW0def
  have hCiH : Ciᴴ = Ci := by
    have h := (cx_posDef (hYpd 0 h0mem)).inv.isHermitian
    rw [cx_inv (hYu 0 h0mem)] at h
    exact h
  have hCiY : Ci * cx (Y 0) = 1 := by
    rw [hCidef, ← cx_mul, nonsing_inv_mul _ (hYu 0 h0mem), cx_one]
  have hBH : (B⁻¹)ᴴ * Bᴴ = 1 := by
    rw [conjTranspose_nonsing_inv]
    exact nonsing_inv_mul _ (by rwa [det_conjTranspose, isUnit_star])
  have hBB : B * B⁻¹ = 1 := mul_nonsing_inv _ hBu
  have hG0 : (F 0)ᴴ * Ci * F 0 = Bᴴ * B := hB
  have hW0H : W0ᴴ = (B⁻¹)ᴴ * ((F 0)ᴴ * Ci) := by
    rw [hW0def, conjTranspose_mul, conjTranspose_mul, hCiH]
  have hW0F0 : W0ᴴ * F 0 = B := by
    calc W0ᴴ * F 0 = (B⁻¹)ᴴ * ((F 0)ᴴ * Ci * F 0) := by rw [hW0H]; simp only [Matrix.mul_assoc]
      _ = B := by rw [hG0, ← Matrix.mul_assoc, hBH, Matrix.one_mul]
  have hM0 : W0ᴴ * cx (Y 0) * W0 = 1 := by
    calc W0ᴴ * cx (Y 0) * W0 = (B⁻¹)ᴴ * ((F 0)ᴴ * (Ci * cx (Y 0)) * Ci * F 0) * B⁻¹ := by
          rw [hW0H, hW0def]; simp only [Matrix.mul_assoc]
      _ = (B⁻¹)ᴴ * (Bᴴ * B) * B⁻¹ := by rw [hCiY, Matrix.mul_one, hG0]
      _ = 1 := by rw [← Matrix.mul_assoc, hBH, Matrix.one_mul, hBB]
  have hW0inj : Function.Injective W0.mulVec := by
    intro v w hvw
    have h : (W0ᴴ * cx (Y 0) * W0) *ᵥ v = (W0ᴴ * cx (Y 0) * W0) *ᵥ w := by
      rw [← mulVec_mulVec, hvw, mulVec_mulVec]
    rwa [hM0, one_mulVec, one_mulVec] at h

  have hh : AnalyticOnNhd ℂ (fun ζ => (W0ᴴ * F ζ).det) (closedBall 0 1) := by
    refine analyticOnNhd_det fun i j => ?_
    intro z hz
    simp only [mul_apply]
    exact Finset.univ.analyticAt_fun_sum fun k _ => analyticAt_const.mul (hF k j z hz)
  have hh0ne : (W0ᴴ * F 0).det ≠ 0 := by rw [hW0F0]; exact hBu.ne_zero

  have hMpd : ∀ ζ ∈ closedBall (0:ℂ) 1, (W0ᴴ * cx (Y ζ) * W0).PosDef := fun ζ hζ =>
    (cx_posDef (hYpd ζ hζ)).conjTranspose_mul_mul_same hW0inj
  have hMdet : ∀ ζ ∈ closedBall (0:ℂ) 1, 0 < (W0ᴴ * cx (Y ζ) * W0).det.re := by
    intro ζ hζ
    have h := MCDet.re_det_pos (hMpd ζ hζ)
    rw [RCLike.re_to_complex] at h
    exact h
  have hMc : ContinuousOn (fun ζ => (W0ᴴ * cx (Y ζ) * W0).det.re) (closedBall 0 1) := by
    have hΦ : Continuous (fun Z : Matrix (Fin g) (Fin g) ℝ =>
        (W0ᴴ * Z.map (fun x : ℝ => (x : ℂ)) * W0).det.re) :=
      Complex.continuous_re.comp
        ((continuous_const.matrix_mul (continuous_id.matrix_map Complex.continuous_ofReal)).matrix_mul
          continuous_const).matrix_det
    have h := hΦ.comp_continuousOn hYc
    simp only [Function.comp_def] at h
    exact h
  have hℓc : ContinuousOn (fun ζ => Real.log (W0ᴴ * cx (Y ζ) * W0).det.re) (closedBall 0 1) :=
    hMc.log fun ζ hζ => (hMdet ζ hζ).ne'
  have hℓint : CircleIntegrable (fun ζ => Real.log (W0ᴴ * cx (Y ζ) * W0).det.re) 0 1 :=
    (hℓc.mono hsph).circleIntegrable zero_le_one

  have hYent : ∀ j k, CircleIntegrable (fun ζ => Y ζ j k) 0 1 := by
    intro j k
    have h := (continuous_id.matrix_elem j k).comp_continuousOn hYc
    simp only [Function.comp_def, id] at h
    exact (h.mono hsph).circleIntegrable zero_le_one
  have hYentc : ∀ j k, CircleIntegrable
      (fun ζ => (∑ a, (star (W0 j a) * W0 k a).re) * Y ζ j k) 0 1 := by
    intro j k
    simpa only [smul_eq_mul] using
      (hYent j k).const_fun_smul (a := ∑ a, (star (W0 j a) * W0 k a).re)
  have htr : ∀ ζ, RCLike.re (W0ᴴ * cx (Y ζ) * W0).trace =
      ∑ j, ∑ k, (∑ a, (star (W0 j a) * W0 k a).re) * Y ζ j k := fun ζ => re_trace_eq W0 (Y ζ)
  have hsum_int : CircleIntegrable
      (fun ζ => ∑ j, ∑ k, (∑ a, (star (W0 j a) * W0 k a).re) * Y ζ j k) 0 1 :=
    CircleIntegrable.fun_sum _ fun j _ => CircleIntegrable.fun_sum _ fun k _ => hYentc j k
  have htravg : circleAverage
      (fun ζ => ∑ j, ∑ k, (∑ a, (star (W0 j a) * W0 k a).re) * Y ζ j k) 0 1 = rk := by
    rw [circleAverage_fun_sum fun j _ => CircleIntegrable.fun_sum _ fun k _ => hYentc j k]
    have hj : ∀ j, circleAverage (fun ζ => ∑ k, (∑ a, (star (W0 j a) * W0 k a).re) * Y ζ j k) 0 1 =
        ∑ k, (∑ a, (star (W0 j a) * W0 k a).re) * Y 0 j k := by
      intro j
      rw [circleAverage_fun_sum fun k _ => hYentc j k]
      refine Finset.sum_congr rfl fun k _ => ?_
      have h := circleAverage_fun_smul (c := (0:ℂ)) (R := 1)
        (a := ∑ a, (star (W0 j a) * W0 k a).re) (f := fun ζ => Y ζ j k)
      simp only [smul_eq_mul] at h
      rw [h, hYmean]
    simp only [hj]
    rw [← htr 0, hM0]
    simp

  have hℓavg : circleAverage (fun ζ => Real.log (W0ᴴ * cx (Y ζ) * W0).det.re) 0 1 ≤ 0 := by
    have hle : ∀ ζ ∈ sphere (0:ℂ) |(1:ℝ)|, Real.log (W0ᴴ * cx (Y ζ) * W0).det.re ≤
        (∑ j, ∑ k, (∑ a, (star (W0 j a) * W0 k a).re) * Y ζ j k) - rk := by
      intro ζ hζ
      have hζ' : ζ ∈ closedBall (0:ℂ) 1 := hsph (by simpa using hζ)
      have h := MCDet.log_re_det_le (hMpd ζ hζ')
      rw [htr ζ, RCLike.re_to_complex, Fintype.card_fin] at h
      exact h
    have hint2 := hsum_int.fun_sub (circleIntegrable_const (rk : ℝ) 0 1)
    calc circleAverage (fun ζ => Real.log (W0ᴴ * cx (Y ζ) * W0).det.re) 0 1
        ≤ circleAverage
          (fun ζ => (∑ j, ∑ k, (∑ a, (star (W0 j a) * W0 k a).re) * Y ζ j k) - rk) 0 1 :=
          circleAverage_mono hℓint hint2 hle
      _ = 0 := by
          rw [circleAverage_fun_sub hsum_int (circleIntegrable_const _ _ _), htravg,
            circleAverage_const]
          ring

  have hpt : ∀ ζ ∈ sphere (0:ℂ) 1, (W0ᴴ * F ζ).det ≠ 0 →
      2 * Real.log ‖(W0ᴴ * F ζ).det‖ - Real.log (W0ᴴ * cx (Y ζ) * W0).det.re ≤
        logDetGram (Y ζ) (F ζ) := by
    intro ζ hζ hhζ
    have hζ' : ζ ∈ closedBall (0:ℂ) 1 := hsph hζ
    have hcs := MCDet.norm_det_mul_sq_le_of_posDef (cx_posDef (hYpd ζ hζ')) (F ζ) W0
    rw [cx_inv (hYu ζ hζ'), RCLike.re_to_complex, RCLike.re_to_complex] at hcs
    have hpos : 0 < ‖(W0ᴴ * F ζ).det‖ ^ 2 := by positivity
    have hlog := Real.log_le_log hpos hcs
    rw [Real.log_mul (hMdet ζ hζ').ne' (hGdet ζ hζ').ne', Real.log_pow] at hlog
    show _ ≤ Real.log ((F ζ)ᴴ * ((Y ζ)⁻¹).map (fun x : ℝ => (x : ℂ)) * F ζ).det.re
    push_cast at hlog
    linarith

  have hφ0 : logDetGram (Y 0) (F 0) ≤ 2 * Real.log ‖(W0ᴴ * F 0).det‖ - 0 := by
    show Real.log ((F 0)ᴴ * Ci * F 0).det.re ≤ _
    rw [sub_zero, hW0F0, hG0]
    have h : (Bᴴ * B).det.re = ‖B.det‖ ^ 2 := by
      rw [det_mul, det_conjTranspose, Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow,
        Complex.ofReal_re]
    rw [h, Real.log_pow]
    push_cast
    linarith
  exact le_circleAverage_of_minorant hh hh0ne hφint hℓint hpt hℓavg hφ0
end LogDetGramSubmean
end GroundTheory.Heights₂.Heights
