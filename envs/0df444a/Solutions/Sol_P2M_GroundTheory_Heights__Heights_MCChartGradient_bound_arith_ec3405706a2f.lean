-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MCChartGradient_bound_arith_ec3405706a2f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:04:41.053767+00:00
-- url     : https://prove2.me/submissions/fef39e3b-a049-457e-b269-71039f71a0ed

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsBounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PChartGradient

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
open GroundTheory.Heights₂.Heights.MCChartGradient
namespace GroundTheory.Heights₂.Heights.MCChartGradient
theorem _root_.solution (S A C₁ δ r e : ℝ) (k : ℕ) (hS : 0 ≤ S) (hA : 0 ≤ A) (hC₁ : 0 < C₁)
    (hδ : 0 < δ) (hr : 0 < r) (he : 1 ≤ e) :
    S * (1 + A * e) / ((C₁ * r)⁻¹ ^ k * δ) ≤ S * (1 + A) * C₁ ^ k / δ * r ^ k * e := by
  have hCr : 0 < C₁ * r := mul_pos hC₁ hr
  have h1 : S * (1 + A * e) / ((C₁ * r)⁻¹ ^ k * δ) =
      S * (1 + A * e) * (C₁ ^ k * r ^ k / δ) := by
    rw [inv_pow, ← mul_pow]
    field_simp
  rw [h1]
  have h2 : S * (1 + A * e) ≤ S * (1 + A) * e := by
    nlinarith [mul_le_mul_of_nonneg_left he hS]
  have h3 : 0 ≤ C₁ ^ k * r ^ k / δ := by positivity
  calc S * (1 + A * e) * (C₁ ^ k * r ^ k / δ) ≤ S * (1 + A) * e * (C₁ ^ k * r ^ k / δ) :=
        mul_le_mul_of_nonneg_right h2 h3
    _ = S * (1 + A) * C₁ ^ k / δ * r ^ k * e := by ring
end GroundTheory.Heights₂.Heights.MCChartGradient
