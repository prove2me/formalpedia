-- Prove2me | solution 1 for ThreeSum.LocalGraph.rightVertices_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:11:13.011889+00:00
-- url     : https://prove2.me/submissions/ec00bbd8-eb72-4a0c-87d9-eae51f81ce06

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
import Theorems.Thm_ThreeSum_LayerCounts_vertices_card


set_option autoImplicit false
open ThreeSum ThreeSum.LocalGraph
variable {α : Type*} [DecidableEq α]
open LayerCounts
variable {L h : ℕ}
namespace ThreeSum.LocalGraph
theorem _root_.solution (L h : ℕ) : (rightVertices L h).card = L.choose h := by
  rw [rightVertices, Finset.card_image_of_injective _ rightWord_injective, vertices_card]
end ThreeSum.LocalGraph
