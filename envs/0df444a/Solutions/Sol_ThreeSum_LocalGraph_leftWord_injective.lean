-- Prove2me | solution 1 for ThreeSum.LocalGraph.leftWord_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:09:04.515818+00:00
-- url     : https://prove2.me/submissions/046005f1-13ad-48e8-bc1d-0a9c2cb7dcb8

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
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices



set_option autoImplicit false
open ThreeSum ThreeSum.LocalGraph
variable {α : Type*} [DecidableEq α]
namespace ThreeSum.LocalGraph
theorem _root_.solution : Function.Injective (@leftWord α _) := by
  intro s t he
  ext i
  simpa only [leftWord, decide_eq_decide] using congrFun he i
end ThreeSum.LocalGraph
