-- Prove2me | solution 1 for ThreeSum.LocalGraph.left_fiber_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:00:06.455639+00:00
-- url     : https://prove2.me/submissions/6a211fe3-45eb-44cb-9e94-2614453f4369

import Definitions.Def_Submission_ThreeSum_LayerCounts
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Bool.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_LocalGraph
import Theorems.Thm_ThreeSum_LocalGraph_leftWord_injective
import Theorems.Thm_ThreeSum_LocalGraph_edge_data
import Theorems.Thm_ThreeSum_LocalGraph_subtype_filter_card
import Definitions.Def_WeightedCache3SUM_Alias_732b95cfaa1b9c22
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices



set_option autoImplicit false
open ThreeSum ThreeSum.LocalGraph
variable {α : Type*} [DecidableEq α]
open LayerCounts
variable {L h : ℕ}
namespace ThreeSum.LocalGraph
theorem _root_.solution (e : Edge L h) :
    (Finset.univ.filter (fun f : Edge L h => left f = left e)).card =
      (L - h).choose h := by
  simp only [left, leftWord_injective.eq_iff]
  exact (subtype_filter_card (edgeSet L h) (fun p => p.1 = e.val.1)).trans
    (leftFiber_card e.val.1 (edge_data e).1)
end ThreeSum.LocalGraph
