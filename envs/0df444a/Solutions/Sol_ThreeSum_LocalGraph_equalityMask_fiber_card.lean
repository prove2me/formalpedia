-- Prove2me | solution 1 for ThreeSum.LocalGraph.equalityMask_fiber_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:01:40.010119+00:00
-- url     : https://prove2.me/submissions/45c69fa6-78d6-481c-be4b-cc0340cefd61

import Definitions.Def_Submission_ThreeSum_LayerCounts
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Bool.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_LocalGraph
import Theorems.Thm_ThreeSum_LocalGraph_output_card
import Theorems.Thm_ThreeSum_LocalGraph_equalityMask_eq_iff
import Theorems.Thm_ThreeSum_LocalGraph_subtype_filter_card
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Definitions.Def_WeightedCache3SUM_Alias_7ecbf42a1119fbd7
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices



set_option autoImplicit false
open ThreeSum ThreeSum.LocalGraph
variable {α : Type*} [DecidableEq α]
open LayerCounts
variable {L h : ℕ}
namespace ThreeSum.LocalGraph
theorem _root_.solution (e : Edge L h) :
    (Finset.univ.filter (fun f : Edge L h => equalityMask f = equalityMask e)).card =
      (2 * h).choose h := by
  simp only [equalityMask_eq_iff, output]
  exact (subtype_filter_card (edgeSet L h) (fun p => p.1 ∪ p.2 = e.val.1 ∪ e.val.2)).trans
    (unionFiber_card (output e) (output_card e))
end ThreeSum.LocalGraph
