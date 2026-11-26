-- Prove2me | solution 1 for closedUniformizerG_cylinder_measurable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:05:36.080537+00:00
-- url     : https://prove2.me/submissions/fc771826-dd52-4a6a-9079-58e2492dabfc

import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Definitions.Def_BicausalOT_DescriptiveSetTheory_AnalyticSigmaAlgebra
import Definitions.Def_BicausalOT_DescriptiveSetTheory_Tree
import Theorems.Thm_analyticSet_projFiberCylNG
import Theorems.Thm_closedUniformizerG_cylinder_eq
import Theorems.Thm_IsOpen_analyticSet
import Theorems.Thm_MeasureTheory_AnalyticSet_compl_mem_analyticMeasurableSpace
import Theorems.Thm_MeasureTheory_AnalyticSet_mem_analyticMeasurableSpace


set_option autoImplicit false
open Set Topology MeasureTheory
open scoped Classical
noncomputable section
variable {X : Type*} [TopologicalSpace X]
theorem _root_.solution [PolishSpace X]
    {F : Set (X × (ℕ → ℕ))} (hF : IsClosed F) (hne : F.Nonempty)
    (f : ℕ → ℕ) (n : ℕ) :
    @MeasurableSet _ (analyticMeasurableSpace X)
      { x | ∀ i < n, closedUniformizerG F hF hne x i = f i } := by
  rw [closedUniformizerG_cylinder_eq hF hne f n]
  apply MeasurableSet.union
  · apply MeasurableSet.inter
    · exact (analyticSet_projFiberCylNG hF f n).mem_analyticMeasurableSpace
    · exact MeasurableSet.iInter fun m =>
        MeasurableSet.iInter fun j =>
          (analyticSet_projFiberCylNG hF _ _).compl_mem_analyticMeasurableSpace
  · apply MeasurableSet.inter
    · exact (hF.analyticSet.image_of_continuous continuous_fst).compl_mem_analyticMeasurableSpace
    · by_cases h : ∀ i < n, hne.some.2 i = f i
      · have : {x : X | ∀ i < n, hne.some.2 i = f i} = univ := by
          ext; simp only [mem_ofPred_eq, mem_univ, iff_true]; exact fun _ hh => h _ hh
        rw [this]; exact @MeasurableSet.univ _ (analyticMeasurableSpace X)
      · have : {x : X | ∀ i < n, hne.some.2 i = f i} = ∅ := by
          ext; simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
          exact fun h' => h (fun i hi => h' i hi)
        rw [this]; exact @MeasurableSet.empty _ (analyticMeasurableSpace X)
