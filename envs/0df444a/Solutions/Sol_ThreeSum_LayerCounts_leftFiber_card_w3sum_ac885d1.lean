-- Prove2me | solution 1 for ThreeSum.LayerCounts.leftFiber_card_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:09:00.877202+00:00
-- url     : https://prove2.me/submissions/5552a9a5-d761-431c-8fec-61d22b043648

import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Choose.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_LayerCounts
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet

set_option autoImplicit false
open ThreeSum ThreeSum.LayerCounts
open Finset
namespace ThreeSum.LayerCounts
theorem _root_.solution {L h : ℕ} (S : Finset (Fin L)) (hS : S.card = h) :
    ((edgeSet L h).filter (fun p => p.1 = S)).card = (L - h).choose h := by
  have hc : ((univ : Finset (Fin L)) \ S).card = L - h := by
    rw [card_sdiff_of_subset (subset_univ S)]
    simp [hS]
  rw [← hc, ← card_powersetCard]
  apply card_bij (fun p _ => p.2)
  · intro p hp
    rcases mem_filter.mp hp with ⟨hp, hpS⟩
    rcases mem_edgeSet.mp hp with ⟨_, hp2, hd⟩
    apply mem_powersetCard.mpr
    refine ⟨?_, hp2⟩
    intro i hi
    apply mem_sdiff.mpr
    refine ⟨mem_univ i, ?_⟩
    intro his
    exact disjoint_left.mp hd (hpS ▸ his) hi
  · intro p hp q hq he
    apply Prod.ext
    · exact (mem_filter.mp hp).2.trans (mem_filter.mp hq).2.symm
    · exact he
  · intro V hV
    rcases mem_powersetCard.mp hV with ⟨hsub, hcard⟩
    refine ⟨(S, V), ?_, rfl⟩
    apply mem_filter.mpr
    refine ⟨mem_edgeSet.mpr ⟨hS, hcard, ?_⟩, rfl⟩
    apply disjoint_left.mpr
    intro i his hiv
    exact (mem_sdiff.mp (hsub hiv)).2 his
end ThreeSum.LayerCounts
