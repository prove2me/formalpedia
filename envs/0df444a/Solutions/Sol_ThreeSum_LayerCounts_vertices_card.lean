-- Prove2me | solution 1 for ThreeSum.LayerCounts.vertices_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:06:43.81921+00:00
-- url     : https://prove2.me/submissions/3fca1180-b9d6-4c9f-a15b-be76e4ef3089

import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Choose.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_LayerCounts
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
attribute [local simp] ThreeSum.LayerCounts.mem_vertices

set_option autoImplicit false
open ThreeSum ThreeSum.LayerCounts
open Finset
namespace ThreeSum.LayerCounts
theorem _root_.solution (L h : ℕ) : (vertices L h).card = L.choose h := by
  simp [vertices, card_powersetCard]
end ThreeSum.LayerCounts
