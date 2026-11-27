-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_VarietyMassLower_proof_99a791b6e958
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:10:54.289349+00:00
-- url     : https://prove2.me/submissions/a254ef59-7e37-482b-b61e-2b551e80d56d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarietyMassLower
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTangentGraphLowerDensity
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarietyTangentGraphDense
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarietyLelongMono
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PVarietyMassLower
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TangentGraphLowerDensity_unitBall_pos_0862738ceb6b


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
open MvPolynomial MeasureTheory
open scoped ENNReal
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace VarietyMassLower
theorem _root_.solution (hG : VarietyTangentGraphDense.Statement)
    (hL : TangentGraphLowerDensity.Statement) (hM : VarietyLelongMono.Statement) :
    VarietyMassLower.Statement := by
  intro n d J hJ hd R
  set τ := μH[((2 * d : ℕ) : ℝ)] (Metric.ball (0 : EuclideanSpace ℂ (Fin d)) 1) with hτdef
  have hτ : 0 < τ := TangentGraphLowerDensity.unitBall_pos d
  set m : ℝ≥0∞ := min τ 1 with hmdef
  have hm0 : 0 < m := lt_min hτ one_pos
  have hmtop : m ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
  have hmτ : m ≤ τ := min_le_left _ _
  have hmr : 0 < m.toReal := ENNReal.toReal_pos hm0.ne' hmtop
  refine ⟨(1 / 2) * (1 / 2) ^ (2 * d) * m.toReal, by positivity, fun z hz _ ρ hρ => ?_⟩
  obtain ⟨hρ0, -⟩ := hρ
  obtain ⟨b, I₀, Ω, V, g, w₀, hcard, hΩ, hV, hw₀, hg, hproj, hZV, htan, hdist⟩ :=
    hG n d J hJ hd z hz (ρ / 2) (by linarith)
  have hz₀ : g w₀ ∈ zeroSetEuc J := by
    have h : g w₀ ∈ g '' Ω := ⟨w₀, hw₀, rfl⟩
    rw [← hZV] at h
    exact h.1
  obtain ⟨r₀, hr₀, hlow⟩ := hL n d b I₀ (zeroSetEuc J) Ω V g w₀ hcard hΩ hV hw₀ hg hproj hZV htan
    (1 / 2) ⟨by norm_num, by norm_num⟩
  set t := min (r₀ / 2) (ρ / 2) with htdef
  have ht0 : 0 < t := lt_min (by linarith) (by linarith)
  have htr : t < r₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hts : t ≤ ρ / 2 := min_le_right _ _
  have h1 := hlow t ⟨ht0, htr⟩
  have h2 := hM n d J hJ hd (g w₀) hz₀ t (ρ / 2) ht0 hts
  have hsub : zeroSetEuc J ∩ Metric.ball (g w₀) (ρ / 2) ⊆ zeroSetEuc J ∩ Metric.ball z ρ :=
    Set.inter_subset_inter_right _ (Metric.ball_subset_ball' (by linarith))
  have h3 := measure_mono (μ := μH[((2 * d : ℕ) : ℝ)]) hsub
  have key : ENNReal.ofReal (t ^ (2 * d)) * (ENNReal.ofReal ((1 / 2) * (ρ / 2) ^ (2 * d)) * τ) ≤
      ENNReal.ofReal (t ^ (2 * d)) * μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc J ∩ Metric.ball (g w₀) (ρ / 2)) := by
    calc ENNReal.ofReal (t ^ (2 * d)) * (ENNReal.ofReal ((1 / 2) * (ρ / 2) ^ (2 * d)) * τ)
        = ENNReal.ofReal ((ρ / 2) ^ (2 * d)) * (ENNReal.ofReal ((1 / 2) * t ^ (2 * d)) * τ) := by
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num)]
          ring
      _ ≤ ENNReal.ofReal ((ρ / 2) ^ (2 * d)) *
            μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc J ∩ Metric.ball (g w₀) t) := by gcongr
      _ ≤ _ := h2
  have key' := (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.2 (pow_pos ht0 _)).ne'
    ENNReal.ofReal_ne_top).1 key
  have hc : (1 / 2) * (1 / 2) ^ (2 * d) * m.toReal * ρ ^ (2 * d) =
      ((1 / 2) * (ρ / 2) ^ (2 * d)) * m.toReal := by
    rw [div_pow, div_pow, one_pow]
    ring
  calc ENNReal.ofReal ((1 / 2) * (1 / 2) ^ (2 * d) * m.toReal * ρ ^ (2 * d))
      = ENNReal.ofReal ((1 / 2) * (ρ / 2) ^ (2 * d)) * m := by
        rw [hc, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hmtop]
    _ ≤ ENNReal.ofReal ((1 / 2) * (ρ / 2) ^ (2 * d)) * τ := by gcongr
    _ ≤ μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc J ∩ Metric.ball (g w₀) (ρ / 2)) := key'
    _ ≤ μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc J ∩ Metric.ball z ρ) := h3
end VarietyMassLower
end GroundTheory.Heights₂.Heights
