-- Prove2me | solution 1 for WeakMFG.Existence.lemma_7_6
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-10-28T18:11:04.980932+00:00
-- url     : https://prove2.me/submissions/ee94ca1d-d807-4eb2-bc24-e65a0cc5e78c

import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal Matrix

theorem solution {E F : Type*} [MeasurableSpace E] [mF : MeasurableSpace F]
    (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hνμ : ν ≪ μ)
    (X : E → F) (hX : Measurable X) :
    (fun x => ((ν.map X).rnDeriv (μ.map X) (X x)).toReal) =ᵐ[μ]
      μ[fun x => (ν.rnDeriv μ x).toReal | MeasurableSpace.comap X mF] := by
  exact MeasureTheory.toReal_rnDeriv_map hνμ hX
