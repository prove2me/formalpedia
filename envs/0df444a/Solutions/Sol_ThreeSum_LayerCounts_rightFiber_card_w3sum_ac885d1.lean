-- Prove2me | solution 1 for ThreeSum.LayerCounts.rightFiber_card_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:00:02.121247+00:00
-- url     : https://prove2.me/submissions/0f167192-005e-4650-8dbb-601e4e4afa02

import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Choose.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_LayerCounts
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Definitions.Def_WeightedCache3SUM_Alias_732b95cfaa1b9c22
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet

set_option autoImplicit false
open ThreeSum ThreeSum.LayerCounts
open Finset
namespace ThreeSum.LayerCounts
theorem _root_.solution {L h : ℕ} (V : Finset (Fin L)) (hV : V.card = h) :
    ((edgeSet L h).filter (fun p => p.2 = V)).card = (L - h).choose h := by
  rw [← leftFiber_card V hV]
  apply card_bij (fun p _ => p.swap)
  · intro p hp
    rcases mem_filter.mp hp with ⟨hp, hpV⟩
    rcases mem_edgeSet.mp hp with ⟨h1, h2, hd⟩
    exact mem_filter.mpr ⟨mem_edgeSet.mpr ⟨h2, h1, hd.symm⟩, hpV⟩
  · intro p hp q hq he
    exact Prod.swap_injective he
  · intro p hp
    rcases mem_filter.mp hp with ⟨hp, hpV⟩
    rcases mem_edgeSet.mp hp with ⟨h1, h2, hd⟩
    exact ⟨p.swap, mem_filter.mpr ⟨mem_edgeSet.mpr ⟨h2, h1, hd.symm⟩, hpV⟩,
      Prod.swap_swap p⟩
end ThreeSum.LayerCounts
