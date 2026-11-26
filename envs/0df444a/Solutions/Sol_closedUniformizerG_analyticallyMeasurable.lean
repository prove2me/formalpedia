-- Prove2me | solution 1 for closedUniformizerG_analyticallyMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:06:12.075645+00:00
-- url     : https://prove2.me/submissions/900e210c-f0ef-4c1a-a03b-f84395534be7

import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Definitions.Def_BicausalOT_DescriptiveSetTheory_AnalyticSigmaAlgebra
import Definitions.Def_BicausalOT_DescriptiveSetTheory_Tree
import Theorems.Thm_closedUniformizerG_cylinder_measurable

set_option autoImplicit false
open Set Topology MeasureTheory
open scoped Classical
noncomputable section
variable {X : Type*} [TopologicalSpace X]
theorem _root_.solution [PolishSpace X]
    {F : Set (X × (ℕ → ℕ))} (hF : IsClosed F) (hne : F.Nonempty) :
    AnalyticallyMeasurable (closedUniformizerG F hF hne) := by
  have hgen : borel (ℕ → ℕ) = MeasurableSpace.generateFrom
      { s | ∃ (x : ℕ → ℕ) (n : ℕ), s = PiNat.cylinder x n } :=
    (PiNat.isTopologicalBasis_cylinders (E := fun _ => ℕ)).borel_eq_generateFrom
  rw [AnalyticallyMeasurable, hgen]
  intro s hs
  induction hs with
  | basic s hs =>
    obtain ⟨f, n, rfl⟩ := hs
    have : closedUniformizerG F hF hne ⁻¹' PiNat.cylinder f n =
        {x | ∀ i < n, closedUniformizerG F hF hne x i = f i} := by
      ext x; simp only [mem_preimage, PiNat.mem_cylinder_iff, mem_ofPred_eq]
    rw [this]; exact closedUniformizerG_cylinder_measurable hF hne f n
  | empty => exact @MeasurableSet.empty _ (analyticMeasurableSpace X)
  | compl _ _ ih => exact ih.compl
  | iUnion _ _ ih => rw [preimage_iUnion]; exact .iUnion ih
