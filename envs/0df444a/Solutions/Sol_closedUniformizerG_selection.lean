-- Prove2me | solution 1 for closedUniformizerG_selection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:04:55.284617+00:00
-- url     : https://prove2.me/submissions/4f492383-9851-4b87-b68c-d5482a4a7075

import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Definitions.Def_BicausalOT_DescriptiveSetTheory_AnalyticSigmaAlgebra
import Definitions.Def_BicausalOT_DescriptiveSetTheory_Tree
import Theorems.Thm_closedFiberG_nonempty_iff
import Theorems.Thm_leftmostBranchG_mem

set_option autoImplicit false
open Set Topology MeasureTheory
open scoped Classical
noncomputable section
variable {X : Type*} [TopologicalSpace X]
theorem _root_.solution
    {F : Set (X × (ℕ → ℕ))} (hF : IsClosed F) (hne : F.Nonempty)
    {x : X} (hx : x ∈ Prod.fst '' F) :
    (x, closedUniformizerG F hF hne x) ∈ F := by
  simp only [closedUniformizerG, dif_pos ((closedFiberG_nonempty_iff F x).mpr hx)]
  exact leftmostBranchG_mem hF x _
