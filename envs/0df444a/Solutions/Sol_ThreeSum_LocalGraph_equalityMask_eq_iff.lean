-- Prove2me | solution 1 for ThreeSum.LocalGraph.equalityMask_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:13:07.83678+00:00
-- url     : https://prove2.me/submissions/b7136a5e-2ffb-47ee-9b81-da552eb2d9a8

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
import Theorems.Thm_ThreeSum_LocalGraph_equalityMask_eq_output

set_option autoImplicit false
open ThreeSum ThreeSum.LocalGraph
variable {α : Type*} [DecidableEq α]
open LayerCounts
variable {L h : ℕ}
namespace ThreeSum.LocalGraph
theorem _root_.solution (e f : Edge L h) :
    equalityMask e = equalityMask f ↔ output e = output f := by
  rw [equalityMask_eq_output, equalityMask_eq_output]
  exact leftWord_injective.eq_iff
end ThreeSum.LocalGraph
