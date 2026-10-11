-- Prove2me | solution 1 for PhysMeasureBasis.cond_diffuse_noAtoms
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T19:00:02.400907+00:00
-- url     : https://prove2.me/submissions/97887124-7ff4-4931-98c5-aef292954517

-- Generated from PhysMeasureBasis.lean — solution of PhysMeasureBasis.cond_diffuse_noAtoms
import Mathlib
import Definitions.Def_PhysMeasureBasis
import Definitions.Def_ChapterA4
open PhysMeasureBasis



open MeasureTheory Set ProbabilityTheory
open scoped ENNReal

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ : Measure α) [IsFiniteMeasure μ]
    (_hpos : μ {x | μ {x} ≠ 0}ᶜ ≠ 0) :
    NullSingletonClass ((μ {x | μ {x} ≠ 0}ᶜ)⁻¹ • μ.restrict {x | μ {x} ≠ 0}ᶜ) := by

  refine ⟨fun x => ?_⟩
  by_cases hx : μ {x} = 0 <;> simp_all +decide
