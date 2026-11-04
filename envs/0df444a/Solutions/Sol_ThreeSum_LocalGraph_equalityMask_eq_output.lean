-- Prove2me | solution 1 for ThreeSum.LocalGraph.equalityMask_eq_output
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:11:10.792497+00:00
-- url     : https://prove2.me/submissions/0508e599-eb73-4011-904b-419db458435b

import Definitions.Def_Submission_ThreeSum_LayerCounts
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Bool.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_LocalGraph
import Theorems.Thm_ThreeSum_LocalGraph_equalityMask_eq_union
import Theorems.Thm_ThreeSum_LocalGraph_edge_data

set_option autoImplicit false
open ThreeSum ThreeSum.LocalGraph
variable {α : Type*} [DecidableEq α]
open LayerCounts
variable {L h : ℕ}
namespace ThreeSum.LocalGraph
theorem _root_.solution (e : Edge L h) :
    equalityMask e = leftWord (output e) :=
  equalityMask_eq_union (edge_data e).2.2
end ThreeSum.LocalGraph
