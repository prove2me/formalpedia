-- Prove2me | solution 1 for analyticSet_projFiberCylNG
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:03:45.513941+00:00
-- url     : https://prove2.me/submissions/5808d3ac-bf0c-4f39-aef8-fffc7592cab6

import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Definitions.Def_BicausalOT_DescriptiveSetTheory_AnalyticSigmaAlgebra
import Definitions.Def_BicausalOT_DescriptiveSetTheory_Tree
import Theorems.Thm_IsOpen_analyticSet


set_option autoImplicit false
open Set Topology MeasureTheory
open scoped Classical
noncomputable section
variable {X : Type*} [TopologicalSpace X]
theorem _root_.solution [PolishSpace X]
    {F : Set (X × (ℕ → ℕ))} (hF : IsClosed F) (f : ℕ → ℕ) (n : ℕ) :
    AnalyticSet (projFiberCylNG F f n) := by
  have : projFiberCylNG F f n =
      Prod.fst '' (F ∩ (univ ×ˢ ⋂ (i : Fin n), { y : ℕ → ℕ | y i = f i })) := by
    ext x; simp only [projFiberCylNG, fiberRestNG, mem_ofPred_eq, mem_image, Prod.exists,
      mem_inter_iff, mem_prod, mem_univ, true_and, mem_iInter]
    constructor
    · rintro ⟨y, h1, h2⟩; exact ⟨x, y, ⟨h1, fun ⟨i, hi⟩ => h2 i hi⟩, rfl⟩
    · rintro ⟨_, y, ⟨h1, h2⟩, rfl⟩; exact ⟨y, h1, fun i hi => h2 ⟨i, hi⟩⟩
  rw [this]
  exact (hF.inter (IsClosed.prod isClosed_univ (isClosed_iInter fun (i : Fin n) =>
    isClosed_eq (continuous_apply (i : ℕ)) continuous_const))
    ).analyticSet.image_of_continuous continuous_fst
