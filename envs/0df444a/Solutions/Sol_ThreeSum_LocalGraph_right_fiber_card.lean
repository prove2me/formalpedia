-- Prove2me | solution 1 for ThreeSum.LocalGraph.right_fiber_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:17:01.399996+00:00
-- url     : https://prove2.me/submissions/0b760e7f-8a38-43da-bfd0-d1b3b5087526

import Definitions.Def_Submission_ThreeSum_LayerCounts
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Bool.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_LocalGraph
import Theorems.Thm_ThreeSum_LocalGraph_rightWord_injective
import Theorems.Thm_ThreeSum_LocalGraph_edge_data
import Theorems.Thm_ThreeSum_LocalGraph_subtype_filter_card
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Definitions.Def_WeightedCache3SUM_Alias_20b6992b2c5d96d1
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices



set_option autoImplicit false
open ThreeSum ThreeSum.LocalGraph
variable {α : Type*} [DecidableEq α]
open LayerCounts
variable {L h : ℕ}
namespace ThreeSum.LocalGraph
theorem _root_.solution (e : Edge L h) :
    (Finset.univ.filter (fun f : Edge L h => right f = right e)).card =
      (L - h).choose h := by
  simp only [right, rightWord_injective.eq_iff]
  exact (subtype_filter_card (edgeSet L h) (fun p => p.2 = e.val.2)).trans
    (rightFiber_card e.val.2 (edge_data e).2.1)
end ThreeSum.LocalGraph
