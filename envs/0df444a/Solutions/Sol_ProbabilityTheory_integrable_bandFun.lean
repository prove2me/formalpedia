-- Prove2me | solution 1 for ProbabilityTheory.integrable_bandFun
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T10:29:04.964019+00:00
-- url     : https://prove2.me/submissions/31b449d5-ef01-4c77-a472-7d6876c72589

import Definitions.Def_LeanLevy_RandomMeasure_TimeSpacePoisson
import Mathlib.MeasureTheory.Integral.Bochner.Set
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Set Topology Complex
open scoped NNReal ENNReal BigOperators
variable {ν : Measure ℝ} [SigmaFinite ν]

theorem solution {A : Set ℝ} (hA : MeasurableSet A)
    (hAsub : A ⊆ Set.Ioo (-1) 1) (hAfin : ν A < ⊤) (s t : ℝ) :
    Integrable ((Set.Ioc s t ×ˢ A).indicator fun p : ℝ × ℝ => p.2)
      ((volume : Measure ℝ).prod ν) := by
  have hbandmeas : MeasurableSet (Set.Ioc s t ×ˢ A) := measurableSet_Ioc.prod hA
  have hbandfin : (volume.prod ν) (Set.Ioc s t ×ˢ A) < ⊤ :=
    volume_prod_Ioc_prod_lt_top (m := ν) (s := s) (t := t) hAfin
  rw [integrable_indicator_iff hbandmeas]
  refine IntegrableOn.of_bound hbandfin measurable_snd.aestronglyMeasurable 1 ?_
  refine (ae_restrict_mem hbandmeas).mono fun p hp => ?_
  obtain ⟨h1, h2⟩ := hAsub hp.2
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ⟨le_of_lt h1, le_of_lt h2⟩
