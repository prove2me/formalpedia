-- Prove2me | solution 1 for WrittenOnTheWallII.GraphConjecture84.PendantGeodesics.tail_separated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:25:04.586583+00:00
-- url     : https://prove2.me/submissions/47d03e42-0693-4bd6-8f06-67eaef34639e

module
public import Mathlib
public import Definitions.Def_Wowii84_LargestInducedTree
public import Definitions.Def_Wowii84_Main
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_reachable_mem_of_adj_closed

set_option autoImplicit false
@[expose] public section
public section
open WrittenOnTheWallII WrittenOnTheWallII.GraphConjecture84
open SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α]
open WrittenOnTheWallII.GraphConjecture84.PendantGeodesics
variable {G : SimpleGraph α} {K : Finset α} (F : PendantGeodesics G K)
namespace WrittenOnTheWallII.GraphConjecture84.PendantGeodesics
theorem _root_.solution (c : ↥(K : Set α)) {z v : α}
    (hz : z ∈ (F.path c).support) (hzc : z ≠ (c : α))
    (hv : v ∉ (F.path c).support) :
    ¬ (G.induce ({(c : α)}ᶜ : Set α)).Reachable
      ⟨z, by simpa using hzc⟩
      ⟨v, by simpa using (show v ≠ (c : α) from fun heq => hv (heq ▸ (F.path c).start_mem_support))⟩ := by
  intro hr
  have hclosed : ∀ u ∈ {y : ↥({(c : α)}ᶜ : Set α) | (y : α) ∈ (F.path c).support},
      ∀ t, (G.induce ({(c : α)}ᶜ : Set α)).Adj u t → (t : α) ∈ (F.path c).support := by
    intro u hu t hut
    exact F.closed c u hu u.property t hut
  exact hv (reachable_mem_of_adj_closed hclosed hr hz)
end WrittenOnTheWallII.GraphConjecture84.PendantGeodesics
