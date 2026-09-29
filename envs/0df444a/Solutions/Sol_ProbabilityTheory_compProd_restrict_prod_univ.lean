-- Prove2me | solution 1 for ProbabilityTheory.compProd_restrict_prod_univ
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-07-31T17:12:51.411954+00:00
-- url     : https://prove2.me/submissions/d1c7fd66-aeb6-47f3-adc2-56d1e464abc3

import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# Restricting a composition-product to a cylinder over the first coordinate

`(μ ⊗ₘ κ).restrict (s ×ˢ univ) = (μ.restrict s) ⊗ₘ κ`.

Conditioning the joint law on an event that depends only on the first coordinate is the same as
conditioning the first marginal and then composing. Mathlib has the corresponding statement for
`Kernel.compProd`; this is the version for a measure composed with a kernel.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

theorem solution {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    (μ : Measure α) [SFinite μ] (κ : Kernel α β) [IsSFiniteKernel κ]
    {s : Set α} (hs : MeasurableSet s) :
    (μ ⊗ₘ κ).restrict (s ×ˢ (univ : Set β)) = (μ.restrict s) ⊗ₘ κ := by
  ext t ht
  rw [Measure.restrict_apply ht,
    Measure.compProd_apply (ht.inter (hs.prod MeasurableSet.univ)),
    Measure.compProd_apply ht,
    ← lintegral_indicator hs]
  refine lintegral_congr fun a ↦ ?_
  by_cases ha : a ∈ s
  · have : Prod.mk a ⁻¹' (t ∩ s ×ˢ (univ : Set β)) = Prod.mk a ⁻¹' t := by
      ext b; simp [ha]
    rw [this, Set.indicator_of_mem ha]
  · have : Prod.mk a ⁻¹' (t ∩ s ×ˢ (univ : Set β)) = (∅ : Set β) := by
      ext b; simp [ha]
    rw [this, Set.indicator_of_notMem ha, measure_empty]
