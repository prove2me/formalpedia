-- Prove2me | solution 1 for ThreeSum.LayerCounts.vertex_degree_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:09:03.335655+00:00
-- url     : https://prove2.me/submissions/4d847500-962d-44cb-a512-4d068041cd08

import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Choose.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_LayerCounts
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet

set_option autoImplicit false
open ThreeSum ThreeSum.LayerCounts
open Finset
namespace ThreeSum.LayerCounts
theorem _root_.solution (L h : ℕ) :
    L.choose h * (L - h).choose h = L.choose (2 * h) * (2 * h).choose h := by
  simpa [show 2 * h - h = h by omega] using
    (Nat.choose_mul (n := L) (k := 2 * h) (s := h) (by omega)).symm
end ThreeSum.LayerCounts
