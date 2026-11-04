-- Prove2me | solution 1 for ThreeSum.LocalGraph.edge_data
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:09:09.100284+00:00
-- url     : https://prove2.me/submissions/0ccf3510-f747-473b-bc08-19166224eb9b

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
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet



set_option autoImplicit false
open ThreeSum ThreeSum.LocalGraph
variable {α : Type*} [DecidableEq α]
open LayerCounts
variable {L h : ℕ}
namespace ThreeSum.LocalGraph
theorem _root_.solution (e : Edge L h) :
    e.val.1.card = h ∧ e.val.2.card = h ∧ Disjoint e.val.1 e.val.2 :=
  mem_edgeSet.mp e.property
end ThreeSum.LocalGraph
