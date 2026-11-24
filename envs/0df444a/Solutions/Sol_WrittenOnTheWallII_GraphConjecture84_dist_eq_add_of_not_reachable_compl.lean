-- Prove2me | solution 1 for WrittenOnTheWallII.GraphConjecture84.dist_eq_add_of_not_reachable_compl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:24:44.491896+00:00
-- url     : https://prove2.me/submissions/66fcea2d-c293-4b92-8fa1-e5fc98915a43

module
public import Mathlib
public import Definitions.Def_Wowii84_LargestInducedTree
public import Definitions.Def_Wowii84_Main
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_dist_add_dist_eq_of_mem_geodesic

set_option autoImplicit false
@[expose] public section
public section
open WrittenOnTheWallII WrittenOnTheWallII.GraphConjecture84
open SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α]
namespace WrittenOnTheWallII.GraphConjecture84
theorem _root_.solution {G : SimpleGraph α} (hG : G.Connected)
    {c a b : α} (ha : a ≠ c) (hb : b ≠ c)
    (hsep : ¬ (G.induce ({c}ᶜ : Set α)).Reachable
      ⟨a, by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using ha⟩
      ⟨b, by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hb⟩) :
    G.dist a b = G.dist a c + G.dist c b := by
  obtain ⟨p, _, hp⟩ := hG.exists_path_of_dist a b
  by_cases hc : c ∈ p.support
  · exact (dist_add_dist_eq_of_mem_geodesic p hp hc).symm
  · have hsub : ∀ z ∈ p.support, z ∈ ({c}ᶜ : Set α) := by
      intro z hz
      have hzc : z ≠ c := by intro heq; exact hc (heq ▸ hz)
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hzc
    exact (hsep ⟨p.induce ({c}ᶜ : Set α) hsub⟩).elim
end WrittenOnTheWallII.GraphConjecture84
