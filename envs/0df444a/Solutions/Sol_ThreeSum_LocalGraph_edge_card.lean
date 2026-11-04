-- Prove2me | solution 1 for ThreeSum.LocalGraph.edge_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:11:13.489597+00:00
-- url     : https://prove2.me/submissions/09359e3e-42d4-4048-b8b2-87902e2180c6

import Definitions.Def_Submission_ThreeSum_LayerCounts
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Bool.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_LocalGraph
import Definitions.Def_WeightedCache3SUM_Alias_b7deb5218012ad6d


set_option autoImplicit false
open ThreeSum ThreeSum.LocalGraph
variable {α : Type*} [DecidableEq α]
open LayerCounts
variable {L h : ℕ}
namespace ThreeSum.LocalGraph
theorem _root_.solution (L h : ℕ) :
    Fintype.card (Edge L h) = L.choose (2 * h) * (2 * h).choose h := by
  rw [Fintype.card_coe, edgeSet_card]
end ThreeSum.LocalGraph
