-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MCBounds_quad_Y_le_6883bb1a140d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:10:51.376085+00:00
-- url     : https://prove2.me/submissions/e616b2fb-5508-4992-913d-d5169196b686

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_DetIneq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_BoundsY
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Bounds
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_one_le_radius_6e45f36c6393
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_cuspTime_le_radius_1eabef2b2104
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_abs_quad_le_949e60e6298d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_dot_self_nonneg_1b107a996ff0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_entrySum_nonneg_e371d83920f8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_quad_nonneg_28912038225c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_quad_sum_15bed5d07f6d


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.MCBounds
open Matrix
open scoped ComplexOrder
noncomputable section
variable (D : PeriodChartData)
namespace GroundTheory.Heights₂.Heights.MCBounds
theorem _root_.solution {z : Fin D.n → ℂ} (hz : z ∈ D.U) (M : ℝ)
    (hM : entrySum ((D.τ0 z).map Complex.im) ≤ M) (x : Fin D.g → ℝ) :
    x ⬝ᵥ (D.Y z *ᵥ x) ≤ (M + ∑ j, entrySum (D.B j)) * D.radius z * (x ⬝ᵥ x) := by
  have hr1 := one_le_radius D hz
  have hxx := dot_self_nonneg x
  have hM0 : 0 ≤ M := (entrySum_nonneg _).trans hM
  simp only [PeriodChartData.Y, chartImag]
  rw [add_mulVec, dotProduct_add, quad_sum]
  have h0 : x ⬝ᵥ ((D.τ0 z).map Complex.im *ᵥ x) ≤ M * D.radius z * (x ⬝ᵥ x) := by
    have h3 := (le_abs_self _).trans (abs_quad_le ((D.τ0 z).map Complex.im) x)
    have h2 : entrySum ((D.τ0 z).map Complex.im) * (x ⬝ᵥ x) ≤ M * D.radius z * (x ⬝ᵥ x) := by
      apply mul_le_mul_of_nonneg_right _ hxx
      nlinarith
    linarith
  have h1 : ∀ j, x ⬝ᵥ ((cuspTime D.a_le z j • D.B j) *ᵥ x) ≤
      entrySum (D.B j) * D.radius z * (x ⬝ᵥ x) := by
    intro j
    rw [smul_mulVec, dotProduct_smul, smul_eq_mul]
    have ht1 := cuspTime_le_radius D hz j
    have hq := (le_abs_self _).trans (abs_quad_le (D.B j) x)
    have hq0 := quad_nonneg (D.B_psd j) x
    have hr0 : 0 ≤ D.radius z := by linarith
    calc cuspTime D.a_le z j * (x ⬝ᵥ (D.B j *ᵥ x)) ≤ D.radius z * (entrySum (D.B j) * (x ⬝ᵥ x)) :=
          mul_le_mul ht1 hq hq0 hr0
      _ = _ := by ring
  have hsum := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => h1 j
  rw [← Finset.sum_mul, ← Finset.sum_mul] at hsum
  linarith
end GroundTheory.Heights₂.Heights.MCBounds
