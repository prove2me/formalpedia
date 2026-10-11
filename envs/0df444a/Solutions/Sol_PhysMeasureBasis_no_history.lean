-- Prove2me | solution 1 for PhysMeasureBasis.no_history
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T18:59:55.601125+00:00
-- url     : https://prove2.me/submissions/3c541580-64c8-4b90-84f2-2e38eb45a6e5

-- Generated from PhysMeasureBasis.lean — solution of PhysMeasureBasis.no_history
import Mathlib
import Definitions.Def_PhysMeasureBasis
import Definitions.Def_ChapterA4
open PhysMeasureBasis



open MeasureTheory Set ProbabilityTheory
open scoped ENNReal

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ) (_hY : ∀ n, Measurable (Y n))
    (hlaw : ∀ n, ∀ y : ℝ, P {ω | Y n ω = y} = 0) (y₀ : ℝ) :
    P {ω | ∃ n, Y n ω = y₀} = 0 := by

  rw [ show { ω | ∃ n, Y n ω = y₀ } = ⋃ n, { ω | Y n ω = y₀ } by ext; aesop ]
  exact MeasureTheory.measure_iUnion_null fun n => hlaw n y₀
