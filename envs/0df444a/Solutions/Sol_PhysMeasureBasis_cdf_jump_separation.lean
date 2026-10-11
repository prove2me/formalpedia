-- Prove2me | solution 1 for PhysMeasureBasis.cdf_jump_separation
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T19:00:00.313336+00:00
-- url     : https://prove2.me/submissions/ae661690-2ff7-42c6-b405-fa8700453b55

-- Generated from PhysMeasureBasis.lean — solution of PhysMeasureBasis.cdf_jump_separation
import Mathlib
import Definitions.Def_PhysMeasureBasis
import Definitions.Def_ChapterA4
open PhysMeasureBasis



open MeasureTheory Set ProbabilityTheory
open scoped ENNReal

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (F G : ℝ → ℝ) (_hF : Monotone F) (_hG : Monotone G)
    (x₀ : ℝ) (hFc : ContinuousAt F x₀) (ε : ℝ) (hε : 0 < ε)
    (hjump : ∀ a b : ℝ, a < x₀ → x₀ < b → G b - G a ≥ ε) :
    ∃ a b : ℚ, (a:ℝ) < b ∧ |(G b - G a) - (F b - F a)| ≥ ε / 2 := by

  have := Metric.continuousAt_iff.mp hFc ( ε / 4 ) ( by positivity );
  obtain ⟨ δ, δ_pos, H ⟩ := this
  rcases exists_rat_btwn ( show x₀ - δ < x₀ by linarith ) with ⟨ a, ha₁, ha₂ ⟩
  rcases exists_rat_btwn ( show x₀ < x₀ + δ by linarith ) with ⟨ b, hb₁, hb₂ ⟩
  use a, b
  norm_num
  refine ⟨by exact_mod_cast ha₂.trans hb₁, ?_⟩
  cases abs_cases (G b - G a - (F b - F a)) <;>
    linarith [hjump a b ha₂ hb₁,
      abs_lt.mp (H (show |↑a - x₀| < δ from abs_lt.mpr ⟨by linarith, by linarith⟩)),
      abs_lt.mp (H (show |↑b - x₀| < δ from abs_lt.mpr ⟨by linarith, by linarith⟩))]
