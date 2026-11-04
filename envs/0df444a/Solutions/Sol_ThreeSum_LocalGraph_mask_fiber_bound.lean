-- Prove2me | solution 1 for ThreeSum.LocalGraph.mask_fiber_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:07:02.988204+00:00
-- url     : https://prove2.me/submissions/4bb523a1-49cb-4187-804e-01e304764ed6

import Definitions.Def_Submission_ThreeSum_LayerCounts
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Bool.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_LocalGraph
import Theorems.Thm_ThreeSum_LocalGraph_equalityMask_fiber_card

set_option autoImplicit false
open ThreeSum ThreeSum.LocalGraph
variable {α : Type*} [DecidableEq α]
open LayerCounts
variable {L h : ℕ}
namespace ThreeSum.LocalGraph
theorem _root_.solution (e : Edge L h) :
    (Finset.univ.filter (fun f : Edge L h =>
      (fun i => left f i == right f i) = (fun i => left e i == right e i))).card ≤
      (2 * h).choose h :=
  (equalityMask_fiber_card e).le
end ThreeSum.LocalGraph
