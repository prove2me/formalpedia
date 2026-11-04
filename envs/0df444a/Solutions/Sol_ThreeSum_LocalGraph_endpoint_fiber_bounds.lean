-- Prove2me | solution 1 for ThreeSum.LocalGraph.endpoint_fiber_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:19:54.177466+00:00
-- url     : https://prove2.me/submissions/7dcdd176-0f90-4952-9b3e-139c573ac15f

import Definitions.Def_Submission_ThreeSum_LayerCounts
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Bool.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_LocalGraph
import Theorems.Thm_ThreeSum_LocalGraph_left_fiber_card
import Theorems.Thm_ThreeSum_LocalGraph_right_fiber_card

set_option autoImplicit false
open ThreeSum ThreeSum.LocalGraph
variable {α : Type*} [DecidableEq α]
open LayerCounts
variable {L h : ℕ}
namespace ThreeSum.LocalGraph
theorem _root_.solution (e : Edge L h) :
    (Finset.univ.filter (fun f : Edge L h => left f = left e)).card ≤
        (L - h).choose h ∧
      (Finset.univ.filter (fun f : Edge L h => right f = right e)).card ≤
        (L - h).choose h := by
  exact ⟨(left_fiber_card e).le, (right_fiber_card e).le⟩
end ThreeSum.LocalGraph
