-- Prove2me | solution 1 for ThreeSum.LocalGraph.vertex_sets_separated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:13:09.236619+00:00
-- url     : https://prove2.me/submissions/5de51644-efb9-4476-9283-65db5821a764

import Definitions.Def_Submission_ThreeSum_LayerCounts
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Bool.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_LocalGraph
import Theorems.Thm_ThreeSum_LocalGraph_leftWord_ne_rightWord
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
attribute [local simp] ThreeSum.LayerCounts.mem_vertices



set_option autoImplicit false
open ThreeSum ThreeSum.LocalGraph
variable {α : Type*} [DecidableEq α]
open LayerCounts
variable {L h : ℕ}
namespace ThreeSum.LocalGraph
theorem _root_.solution (hsep : 2 * h < L)
    (s : Fin L → Bool) (hs : s ∈ leftVertices L h)
    (t : Fin L → Bool) (ht : t ∈ rightVertices L h) : s ≠ t := by
  obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hs
  obtain ⟨V, hV, rfl⟩ := Finset.mem_image.mp ht
  exact leftWord_ne_rightWord (mem_vertices.mp hS) (mem_vertices.mp hV) hsep
end ThreeSum.LocalGraph
