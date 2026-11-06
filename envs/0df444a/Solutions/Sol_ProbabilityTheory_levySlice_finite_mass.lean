-- Prove2me | solution 1 for ProbabilityTheory.levySlice_finite_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T10:02:14.679256+00:00
-- url     : https://prove2.me/submissions/a2258b40-b492-4897-b18c-c800f65a2c5d

import Definitions.Def_LeanLevy_RandomMeasure_LevyJumpPath
import Definitions.Def_LeanLevy_Levy_LevyMeasure
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Theorems.Thm_ProbabilityTheory_IsLevyMeasure_isFiniteMeasure_restrict_largeSet
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic.Positivity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

theorem solution {ν : Measure ℝ} [SigmaFinite ν] (hν : IsLevyMeasure ν) (j : ℕ) :
    ν (levySlice hν j) < ⊤ := by
  let ε : ℝ := ((levyTruncationSeq hν (j + 1) : ℝ) + 1)⁻¹
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  haveI : IsFiniteMeasure (ν.restrict (largeSet ε)) :=
    IsLevyMeasure.isFiniteMeasure_restrict_largeSet hν hε
  have hmeas : MeasurableSet (largeSet ε) :=
    (isClosed_Ici.preimage continuous_abs).measurableSet
  have hfinite : ν (largeSet ε) < ⊤ := by
    have h := (‹IsFiniteMeasure (ν.restrict (largeSet ε))›).measure_univ_lt_top
    rw [Measure.restrict_apply' hmeas] at h
    simpa only [Set.univ_inter] using h
  have hsub : levySlice hν j ⊆ largeSet ε :=
    (Set.sdiff_subset).trans Set.inter_subset_right
  exact (measure_mono hsub).trans_lt hfinite
