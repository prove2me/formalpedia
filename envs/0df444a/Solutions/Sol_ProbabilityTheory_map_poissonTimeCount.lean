-- Prove2me | solution 1 for ProbabilityTheory.map_poissonTimeCount
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T21:46:19.45888+00:00
-- url     : https://prove2.me/submissions/1bd28cdf-0a09-4709-9b6a-44145e82b5e3

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_TimeSpacePoisson
import Theorems.Thm_ProbabilityTheory_map_poissonRandomMeasure_apply
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Complex ComplexConjugate Set Filter Topology Finset ProbabilityTheory
open scoped NNReal ENNReal
variable {Ω E : Type} [MeasurableSpace E] [MeasurableSpace Ω] [Nonempty E] {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → ℝ × E} {m : Measure E} [SigmaFinite m] {μ : Measure Ω} {A : Set E} {s t : ℝ}

theorem solution [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X (volume.prod m) μ) (hA : MeasurableSet A)
    (hfin : m A < ⊤) (ht : 0 ≤ t) :
    μ.map (poissonTimeCount K X A t)
      = (poissonMeasure (ENNReal.ofReal t * m A).toNNReal).map (Nat.cast : ℕ → ℝ≥0∞) := by
  have hmass : (volume.prod m) (Set.Ioc 0 t ×ˢ A) =
      ENNReal.ofReal (t - 0) * m A := by
    rw [Measure.prod_prod, Real.volume_Ioc]
  have hfinBand : (volume.prod m) (Set.Ioc 0 t ×ˢ A) < ⊤ := by
    rw [hmass]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin
  unfold poissonTimeCount
  rw [ProbabilityTheory.map_poissonRandomMeasure_apply hd
    (measurableSet_Ioc.prod hA) hfinBand, hmass, sub_zero]
