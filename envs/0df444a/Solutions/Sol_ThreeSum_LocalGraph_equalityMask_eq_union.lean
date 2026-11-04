-- Prove2me | solution 1 for ThreeSum.LocalGraph.equalityMask_eq_union
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:09:07.947409+00:00
-- url     : https://prove2.me/submissions/e865456d-5e6a-48cf-ab49-47271fa6bac5

import Definitions.Def_Submission_ThreeSum_LayerCounts
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Bool.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_LocalGraph
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices



set_option autoImplicit false
open ThreeSum ThreeSum.LocalGraph
variable {α : Type*} [DecidableEq α]
namespace ThreeSum.LocalGraph
theorem _root_.solution {s v : Finset α} (hd : Disjoint s v) :
    (fun i => leftWord s i == rightWord v i) = leftWord (s ∪ v) := by
  funext i
  have hnot := Finset.disjoint_left.mp hd
  by_cases hs : i ∈ s <;> by_cases hv : i ∈ v <;>
    simp_all [leftWord, rightWord]
end ThreeSum.LocalGraph
