-- Prove2me | solution 1 for TemporalVoter.lemma_2_5
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T19:55:06.252403+00:00
-- url     : https://prove2.me/submissions/152ff30f-8222-4ba5-b896-e30276c4d011

import Mathlib

open MeasureTheory

theorem solution {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℕ m0} {M N : ℕ → Ω → ℝ} (hM : Martingale M ℱ P) (hN : Martingale N ℱ P) :
    Supermartingale (fun t ω => min (M t ω) (N t ω)) ℱ P := by
  refine ⟨fun t => ?_, fun i j hij => ?_, fun t => ?_⟩
  · letI : MeasurableSpace Ω := ℱ t
    exact (hM.stronglyAdapted t).inf (hN.stronglyAdapted t)
  · have hmin : Integrable (fun ω => min (M j ω) (N j ω)) P :=
      (hM.integrable j).inf (hN.integrable j)
    have h1 := condExp_mono (m := ℱ i) hmin (hM.integrable j)
      (Filter.Eventually.of_forall (fun ω => min_le_left (M j ω) (N j ω)))
    have h2 := condExp_mono (m := ℱ i) hmin (hN.integrable j)
      (Filter.Eventually.of_forall (fun ω => min_le_right (M j ω) (N j ω)))
    filter_upwards [h1, h2, hM.condExp_ae_eq hij, hN.condExp_ae_eq hij] with ω h1 h2 h3 h4
    exact le_min (h1.trans h3.le) (h2.trans h4.le)
  · exact (hM.integrable t).inf (hN.integrable t)
