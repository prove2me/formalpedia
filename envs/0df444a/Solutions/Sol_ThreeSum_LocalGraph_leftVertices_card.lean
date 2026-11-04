-- Prove2me | solution 1 for ThreeSum.LocalGraph.leftVertices_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:11:11.955001+00:00
-- url     : https://prove2.me/submissions/82e07aa7-fd0c-4de2-89ed-010b641204b0

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
import Theorems.Thm_ThreeSum_LayerCounts_vertices_card


set_option autoImplicit false
open ThreeSum ThreeSum.LocalGraph
variable {α : Type*} [DecidableEq α]
open LayerCounts
variable {L h : ℕ}
namespace ThreeSum.LocalGraph
theorem _root_.solution (L h : ℕ) : (leftVertices L h).card = L.choose h := by
  rw [leftVertices, Finset.card_image_of_injective _ leftWord_injective, vertices_card]
end ThreeSum.LocalGraph
