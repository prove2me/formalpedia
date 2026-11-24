-- Prove2me | solution 1 for WrittenOnTheWallII.GraphConjecture84.conjecture84_proof
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:43:04.571573+00:00
-- url     : https://prove2.me/submissions/0b8bc123-0be1-475b-b503-76dcaeccabd6

module
public import Mathlib
public import Definitions.Def_Wowii84_LargestInducedTree
public import Definitions.Def_Wowii84_Main
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_radius_add_one_le_largestInducedTreeSize
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_largestInducedTreeSize_le_card
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_exists_cut_vertex_of_minDegree_eq_one
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_two_mul_radius_le_largestInducedTreeSize_of_isTree
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_radius_add_two_le_largestInducedTreeSize_of_leaf
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_two_mul_radius_le_largestInducedTreeSize_of_cut_vertex

set_option autoImplicit false
@[expose] public section
public section
open WrittenOnTheWallII WrittenOnTheWallII.GraphConjecture84
open SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α]
namespace WrittenOnTheWallII.GraphConjecture84
theorem _root_.solution {β : Type*} [Fintype β] [DecidableEq β] [Nontrivial β]
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (h : G.Connected) (hδ : 0 < G.minDegree) :
    2 * (G.radius.toNat : ℝ) / (G.minDegree : ℝ) ≤ (largestInducedTreeSize G : ℝ) := by
  have htree := radius_add_one_le_largestInducedTreeSize h
  have htreeR : (G.radius.toNat : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) := by
    exact_mod_cast htree
  have hδR : (0 : ℝ) < G.minDegree := by exact_mod_cast hδ
  apply (div_le_iff₀ hδR).2
  by_cases htwo : 2 ≤ G.minDegree
  · have htwoR : (2 : ℝ) ≤ G.minDegree := by exact_mod_cast htwo
    nlinarith [show (0 : ℝ) ≤ (G.radius.toNat : ℝ) from Nat.cast_nonneg _,
      show (0 : ℝ) ≤ (largestInducedTreeSize G : ℝ) from Nat.cast_nonneg _]
  have hδone : G.minDegree = 1 := by omega
  rw [hδone, Nat.cast_one, mul_one]
  by_cases hr : G.radius.toNat ≤ 1
  · have hrR : (G.radius.toNat : ℝ) ≤ 1 := by exact_mod_cast hr
    linarith
  have hr : 2 ≤ G.radius.toNat := by omega
  obtain ⟨u, hu⟩ := G.exists_minimal_degree_vertex
  have hleaf : G.degree u = 1 := hu.symm.trans hδone
  have hmore := radius_add_two_le_largestInducedTreeSize_of_leaf h hleaf hr
  by_cases hr2 : G.radius.toNat ≤ 2
  · have hfinal : 2 * G.radius.toNat ≤ largestInducedTreeSize G := by omega
    exact_mod_cast hfinal
  have hcard : 3 ≤ Fintype.card β := by
    have hle := largestInducedTreeSize_le_card G
    omega
  obtain ⟨v, hv⟩ := exists_cut_vertex_of_minDegree_eq_one hδone hcard
  by_cases hT : G.IsTree
  · have hbound := two_mul_radius_le_largestInducedTreeSize_of_isTree hT
    exact_mod_cast hbound
  have hbound := two_mul_radius_le_largestInducedTreeSize_of_cut_vertex h ⟨v, hv⟩
  exact_mod_cast hbound
end WrittenOnTheWallII.GraphConjecture84
