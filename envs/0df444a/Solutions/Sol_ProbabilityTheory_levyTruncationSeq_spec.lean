-- Prove2me | solution 1 for ProbabilityTheory.levyTruncationSeq_spec
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T10:42:09.792527+00:00
-- url     : https://prove2.me/submissions/df850a4f-f5a1-49e5-9f4a-e1d48d7f6355

import Definitions.Def_LeanLevy_RandomMeasure_LevyJumpPath
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory Filter Set Topology Complex
open scoped NNReal ENNReal BigOperators

theorem solution :
    ∀ {ν : Measure ℝ} [SigmaFinite ν] (hν : IsLevyMeasure ν),
      StrictMono (levyTruncationSeq hν) ∧
        ∀ j : ℕ, (∫⁻ x in Set.Ioo (-1 : ℝ) 1 \ levyAnnulus (levyTruncationSeq hν j),
          ENNReal.ofReal (x ^ 2) ∂ν) ≤ (16 : ℝ≥0∞)⁻¹ ^ j := by
  intro ν hσ hν
  change (fun φ : ℕ → ℕ =>
    StrictMono φ ∧
      ∀ j : ℕ, (∫⁻ x in Set.Ioo (-1 : ℝ) 1 \ levyAnnulus (φ j),
        ENNReal.ofReal (x ^ 2) ∂ν) ≤ (16 : ℝ≥0∞)⁻¹ ^ j) (levyTruncationSeq hν)
  unfold levyTruncationSeq
  exact @Exists.choose_spec (ℕ → ℕ)
    (fun φ => StrictMono φ ∧ ∀ j : ℕ,
      (∫⁻ x in Set.Ioo (-1 : ℝ) 1 \ levyAnnulus (φ j),
        ENNReal.ofReal (x ^ 2) ∂ν) ≤ (16 : ℝ≥0∞)⁻¹ ^ j) _
