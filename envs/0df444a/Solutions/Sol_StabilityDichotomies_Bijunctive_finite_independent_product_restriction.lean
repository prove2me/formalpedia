-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.finite_independent_product_restriction
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:37:46.489282+00:00
-- url     : https://prove2.me/submissions/d1217bc0-95bb-453f-92b0-8d3e07f55d2e

import Mathlib
noncomputable section
open scoped Classical
open MeasureTheory ProbabilityTheory Set

theorem solution {α : Type} [Fintype α]
    (s : Finset α) (μ : α → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] :
    MeasurePreserving (fun x : α → ℝ => fun i : ↥s => x i)
      (Measure.pi μ) (Measure.pi (fun i : ↥s => μ i)) := by
  classical
  letI : Fintype ↥s := Subtype.fintype (fun i => i ∈ s)
  haveI : IsProbabilityMeasure (Measure.pi (fun i : {i // i ∉ s} => μ i)) := by infer_instance
  have h := (measurePreserving_fst : MeasurePreserving Prod.fst
    ((Measure.pi (fun i : {i // i ∈ s} => μ i)).prod (Measure.pi (fun i : {i // i ∉ s} => μ i)))
    (Measure.pi (fun i : {i // i ∈ s} => μ i))).comp
      (measurePreserving_piEquivPiSubtypeProd μ (fun i => i ∈ s))
  convert h using 1
  · rfl
  · congr 1
    exact Subsingleton.elim _ _
