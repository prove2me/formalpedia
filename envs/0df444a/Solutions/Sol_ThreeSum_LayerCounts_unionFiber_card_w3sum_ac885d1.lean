-- Prove2me | solution 1 for ThreeSum.LayerCounts.unionFiber_card_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:09:02.14321+00:00
-- url     : https://prove2.me/submissions/8978e69b-f35e-4442-ac42-d0c85be633c5

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
theorem _root_.solution {L h : ℕ} (Q : Finset (Fin L)) (hQ : Q.card = 2 * h) :
    ((edgeSet L h).filter (fun p => p.1 ∪ p.2 = Q)).card = (2 * h).choose h := by
  rw [← hQ, ← card_powersetCard]
  apply card_bij (fun p _ => p.1)
  · intro p hp
    rcases mem_filter.mp hp with ⟨hp, hpQ⟩
    exact mem_powersetCard.mpr ⟨hpQ ▸ subset_union_left, (mem_edgeSet.mp hp).1⟩
  · intro p hp q hq he
    rcases mem_filter.mp hp with ⟨hp, hpQ⟩
    rcases mem_filter.mp hq with ⟨hq, hqQ⟩
    have hpV : Q \ p.1 = p.2 := by
      rw [← hpQ]
      exact union_sdiff_cancel_left (mem_edgeSet.mp hp).2.2
    have hqV : Q \ q.1 = q.2 := by
      rw [← hqQ]
      exact union_sdiff_cancel_left (mem_edgeSet.mp hq).2.2
    exact Prod.ext he (by rw [← hpV, ← hqV, he])
  · intro S hS
    rcases mem_powersetCard.mp hS with ⟨hsub, hcard⟩
    refine ⟨(S, Q \ S), ?_, rfl⟩
    apply mem_filter.mpr
    refine ⟨mem_edgeSet.mpr ⟨hcard, ?_, ?_⟩, union_sdiff_of_subset hsub⟩
    · rw [card_sdiff_of_subset hsub, hQ, hcard]
      omega
    · exact disjoint_sdiff_self_right
end ThreeSum.LayerCounts
