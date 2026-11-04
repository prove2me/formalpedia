-- Prove2me | solution 1 for ThreeSum.LocalGraph.cross_separated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:13:06.842643+00:00
-- url     : https://prove2.me/submissions/b1771240-9ede-4906-b757-db79acec0374

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
import Theorems.Thm_ThreeSum_LocalGraph_edge_data

set_option autoImplicit false
open ThreeSum ThreeSum.LocalGraph
variable {α : Type*} [DecidableEq α]
open LayerCounts
variable {L h : ℕ}
namespace ThreeSum.LocalGraph
theorem _root_.solution (hsep : 2 * h < L) (e f : Edge L h) : left e ≠ right f :=
  leftWord_ne_rightWord (edge_data e).1 (edge_data f).2.1 hsep
end ThreeSum.LocalGraph
