-- Prove2me | solution 1 for ThreeSum.LocalGraph.leftWord_ne_rightWord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:11:06.111051+00:00
-- url     : https://prove2.me/submissions/cd7ecee7-07fd-4d83-9aa0-8ef3beb8b220

import Definitions.Def_Submission_ThreeSum_LayerCounts
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Bool.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_LocalGraph
import Theorems.Thm_ThreeSum_LocalGraph_leftWord_eq_rightWord_iff
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices



set_option autoImplicit false
open ThreeSum ThreeSum.LocalGraph
variable {α : Type*} [DecidableEq α]
namespace ThreeSum.LocalGraph
theorem _root_.solution {L h : ℕ} {s v : Finset (Fin L)}
    (hs : s.card = h) (hv : v.card = h) (hsep : 2 * h < L) :
    leftWord s ≠ rightWord v := by
  intro he
  have hc := congrArg Finset.card ((leftWord_eq_rightWord_iff s v).mp he)
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ v)] at hc
  simp only [Finset.card_univ, Fintype.card_fin, hs, hv] at hc
  omega
end ThreeSum.LocalGraph
