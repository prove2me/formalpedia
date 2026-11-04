-- Prove2me | solution 1 for ThreeSum.LocalGraph.left_mem_vertices
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:11:14.094733+00:00
-- url     : https://prove2.me/submissions/c16e67ad-3f1f-4752-92ef-0a4bc92448e7

import Definitions.Def_Submission_ThreeSum_LayerCounts
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Bool.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_LocalGraph
import Theorems.Thm_ThreeSum_LocalGraph_edge_data
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
attribute [local simp] ThreeSum.LayerCounts.mem_vertices



set_option autoImplicit false
open ThreeSum ThreeSum.LocalGraph
variable {α : Type*} [DecidableEq α]
open LayerCounts
variable {L h : ℕ}
namespace ThreeSum.LocalGraph
theorem _root_.solution (e : Edge L h) : left e ∈ leftVertices L h :=
  Finset.mem_image.mpr ⟨e.val.1, mem_vertices.mpr (edge_data e).1, rfl⟩
end ThreeSum.LocalGraph
