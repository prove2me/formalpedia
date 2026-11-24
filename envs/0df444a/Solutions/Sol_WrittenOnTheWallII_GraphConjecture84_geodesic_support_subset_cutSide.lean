-- Prove2me | solution 1 for WrittenOnTheWallII.GraphConjecture84.geodesic_support_subset_cutSide
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:28:18.648698+00:00
-- url     : https://prove2.me/submissions/5aba8472-ce89-422f-af8d-d9a247c674d0

module
public import Mathlib
public import Definitions.Def_Wowii84_LargestInducedTree
public import Definitions.Def_Wowii84_Main
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_dist_add_dist_eq_of_mem_geodesic
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_reachable_compl_of_mem_geodesic

set_option autoImplicit false
@[expose] public section
public section
open WrittenOnTheWallII WrittenOnTheWallII.GraphConjecture84
open SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α]
namespace WrittenOnTheWallII.GraphConjecture84
theorem _root_.solution {G : SimpleGraph α} (hG : G.Connected)
    {c v : α} (a : ↥({c}ᶜ : Set α)) (hv : v ∈ cutSide G c a)
    (p : G.Walk c v) (hp : p.length = G.dist c v) :
    ∀ z ∈ p.support, z ∈ cutSide G c a := by
  intro z hz
  by_cases hzc : z = c
  · exact Or.inl hzc
  · refine Or.inr ⟨hzc, ?_⟩
    have hvc : v ≠ c := by
      intro heq
      have hsum := dist_add_dist_eq_of_mem_geodesic p hp hz
      have hdist : G.dist c z = 0 := by simp only [heq, dist_self] at hsum; omega
      exact hzc (hG.dist_eq_zero_iff.mp hdist).symm
    rcases hv with hvc' | ⟨_, hv⟩
    · exact (hvc hvc').elim
    · exact hv.trans (reachable_compl_of_mem_geodesic p hp hvc hz hzc).symm
end WrittenOnTheWallII.GraphConjecture84
