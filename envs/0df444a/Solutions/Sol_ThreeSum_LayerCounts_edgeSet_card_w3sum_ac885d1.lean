-- Prove2me | solution 1 for ThreeSum.LayerCounts.edgeSet_card_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:00:04.884888+00:00
-- url     : https://prove2.me/submissions/8b7c0602-cbcc-489a-86dd-dd7f02b496eb

import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Choose.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_LayerCounts
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_LayerCounts_vertices_card
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Definitions.Def_WeightedCache3SUM_Alias_732b95cfaa1b9c22
import Theorems.Thm_ThreeSum_LayerCounts_vertex_degree_identity
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet

set_option autoImplicit false
open ThreeSum ThreeSum.LayerCounts
open Finset
namespace ThreeSum.LayerCounts
theorem _root_.solution (L h : ℕ) :
    (edgeSet L h).card = L.choose (2 * h) * (2 * h).choose h := by
  calc
    (edgeSet L h).card =
        ∑ S ∈ vertices L h, ((edgeSet L h).filter (fun p => p.1 = S)).card := by
      apply card_eq_sum_card_fiberwise
      intro p hp
      exact mem_vertices.mpr (mem_edgeSet.mp hp).1
    _ = ∑ S ∈ vertices L h, (L - h).choose h := by
      apply sum_congr rfl
      intro S hS
      exact leftFiber_card S (mem_vertices.mp hS)
    _ = L.choose h * (L - h).choose h := by
      simp [vertices_card]
    _ = _ := vertex_degree_identity L h
end ThreeSum.LayerCounts
