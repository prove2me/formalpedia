-- Prove2me | solution 1 for ThreeSum.LocalGraph.leftWord_eq_rightWord_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:09:06.82444+00:00
-- url     : https://prove2.me/submissions/1232badf-11e9-4a66-8635-63609a2c442d

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
theorem _root_.solution [Fintype α] (s v : Finset α) :
    leftWord s = rightWord v ↔ s = Finset.univ \ v := by
  constructor
  · intro he
    ext i
    have hi := congrFun he i
    simpa only [leftWord, rightWord, decide_eq_decide, Finset.mem_sdiff,
      Finset.mem_univ, true_and] using hi
  · intro he
    subst s
    funext i
    simp only [leftWord, rightWord, Finset.mem_sdiff, Finset.mem_univ, true_and]
end ThreeSum.LocalGraph
