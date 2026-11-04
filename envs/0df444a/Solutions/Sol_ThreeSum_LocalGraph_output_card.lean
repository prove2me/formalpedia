-- Prove2me | solution 1 for ThreeSum.LocalGraph.output_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:11:08.37816+00:00
-- url     : https://prove2.me/submissions/0f25409a-f84d-482d-a6b8-999a27508144

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

set_option autoImplicit false
open ThreeSum ThreeSum.LocalGraph
variable {α : Type*} [DecidableEq α]
open LayerCounts
variable {L h : ℕ}
namespace ThreeSum.LocalGraph
theorem _root_.solution (e : Edge L h) : (output e).card = 2 * h := by
  rw [output, Finset.card_union_of_disjoint (edge_data e).2.2,
    (edge_data e).1, (edge_data e).2.1]
  omega
end ThreeSum.LocalGraph
