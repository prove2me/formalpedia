-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_integral_comp_div_sq_378fa9759947
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:48:09.566076+00:00
-- url     : https://prove2.me/submissions/8c35e814-4dbf-4a06-9526-f583a4d2f6c0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegRadialWeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjectionCluster
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegLelongAnnulus

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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff
noncomputable section
open GroundTheory.Heights₂.Heights.RegLelongAnnulus
namespace GroundTheory.Heights₂.Heights.RegLelongAnnulus
theorem _root_.solution (e : ℕ) (h : ℝ → ℝ) {ρ : ℝ} (hρ : ρ ≠ 0) (t : ℝ) :
    ∫ τ in (0 : ℝ)..t, h (τ / ρ ^ 2) * (((e + 1 : ℕ) : ℝ) * τ ^ (e + 1 - 1)) =
      ρ ^ (2 * (e + 1)) * ∫ w in (0 : ℝ)..t / ρ ^ 2, h w * (((e + 1 : ℕ) : ℝ) * w ^ (e + 1 - 1)) := by
  have hρ2 : ρ ^ 2 ≠ 0 := pow_ne_zero 2 hρ
  obtain ⟨G, hG⟩ : ∃ G : ℝ → ℝ, G = fun w => h w * (((e + 1 : ℕ) : ℝ) * w ^ (e + 1 - 1)) := ⟨_, rfl⟩
  have key : ∀ τ : ℝ, h (τ / ρ ^ 2) * (((e + 1 : ℕ) : ℝ) * τ ^ (e + 1 - 1)) =
      ρ ^ (2 * e) * G (τ / ρ ^ 2) := by
    intro τ
    rw [hG]
    simp only [Nat.add_sub_cancel]
    rw [div_pow, ← pow_mul]
    field_simp
  have key2 : ∀ w : ℝ, h w * (((e + 1 : ℕ) : ℝ) * w ^ (e + 1 - 1)) = G w := fun w => by rw [hG]
  simp only [key, key2]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_div G hρ2, zero_div, smul_eq_mul]
  ring
end GroundTheory.Heights₂.Heights.RegLelongAnnulus
