-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartGradient_proof_7e82c1566517
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:53:46.240771+00:00
-- url     : https://prove2.me/submissions/cda36217-ff43-4fea-918d-ef8dd2af5173

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsBounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PChartGradient
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCChartGradient_u_eq_daf79c38bffd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCChartGradient_bound_arith_ec3405706a2f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCChartGradient_pow_le_rpow_of_le_97306c4f015b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_exists_gram_bounds_e2da112e7cba
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_one_le_radius_6e45f36c6393


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
open Matrix
noncomputable section
open MCChartGradient
namespace GroundTheory.Heights₂.Heights
namespace ChartGradient
theorem _root_.solution (h₁ : LogDetGramDeriv.Statement) (h₂ : ChartFrameDeriv.Statement)
    (h₃ : ChartImagDeriv.Statement) (h₄ : ChartBounds.Statement) : ChartGradient.Statement := by
  intro D
  obtain ⟨K₀, hK₀, hK⟩ := h₁ D.g D.rk
  obtain ⟨AF, hAF, hF⟩ := h₂ D
  obtain ⟨AY, hAY, hY⟩ := h₃ D
  obtain ⟨C₁, hC₁, hB⟩ := h₄ D
  obtain ⟨δ, M, hδ, -, hG⟩ := MCBounds.exists_gram_bounds D
  have hc : 0 ≤ D.c⁻¹ := inv_nonneg.mpr D.c_pos.le
  set S : ℝ := K₀ * (1 + AF) ^ (2 * D.rk) * (1 + D.c⁻¹) ^ (D.rk + 1) with hSdef
  have hS : 0 ≤ S := by positivity
  set K' : ℝ := S * (1 + AY) * C₁ ^ D.rk / δ with hK'def
  have hK'0 : 0 ≤ K' := by positivity
  have hC1 : (1 : ℝ) ≤ max K' (max (D.rk : ℝ) 1) := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨max K' (max (D.rk : ℝ) 1), lt_of_lt_of_le one_pos hC1, fun p hp hps => ?_⟩
  set C := max K' (max (D.rk : ℝ) 1) with hCdef
  have hz : p.1 ∈ D.U := (D.K_subset hp).1
  have hr1 : 1 ≤ D.radius p.1 := MCBounds.one_le_radius D hz
  set r := D.radius p.1 with hr
  have hr0 : 0 < r := lt_of_lt_of_le one_pos hr1
  have he : 1 ≤ Real.exp (r / 2) := Real.one_le_exp (by linarith)
  obtain ⟨hYc, -, hdet, -, -, -⟩ := hB p hp hps
  have hCr : 0 < C₁ * r := mul_pos hC₁ hr0
  have hμpos : 0 < (C₁ * r)⁻¹ ^ D.rk * δ := mul_pos (pow_pos (inv_pos.mpr hCr) _) hδ
  have hμ : (C₁ * r)⁻¹ ^ D.rk * δ ≤
      ((D.f p)ᴴ * (D.Y p.1)⁻¹.map (fun x : ℝ => (x : ℂ)) * D.f p).det.re :=
    le_trans (mul_le_mul_of_nonneg_left (hG p hp).1 (pow_nonneg (inv_pos.mpr hCr).le _)) hdet
  obtain ⟨hd, hn⟩ := hK (E := (Fin D.n → ℂ) × (Fin D.m → ℂ)) D.f (fun q => D.Y q.1) p AF
    (AY * Real.exp (r / 2)) D.c ((C₁ * r)⁻¹ ^ D.rk * δ) D.c_pos hμpos hAF.le
    (mul_nonneg hAY.le (Real.exp_pos _).le) (hF p hp) (fun j l => hY p hp hps j l) hYc hμ
  rw [u_eq]
  refine ⟨hd, hn.trans ?_⟩
  have hb := bound_arith S AY C₁ δ r (Real.exp (r / 2)) D.rk hS hAY.le hC₁ hδ hr0 he
  refine hb.trans ?_
  have hpow : r ^ D.rk ≤ r ^ C :=
    pow_le_rpow_of_le hr1 ((le_max_left _ _).trans (le_max_right _ _))
  have hKC : K' ≤ C := le_max_left _ _
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul hKC hpow (pow_nonneg hr0.le _) (by linarith)) (Real.exp_pos _).le
end ChartGradient
end GroundTheory.Heights₂.Heights
