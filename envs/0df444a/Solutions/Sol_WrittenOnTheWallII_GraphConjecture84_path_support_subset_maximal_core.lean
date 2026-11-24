-- Prove2me | solution 1 for WrittenOnTheWallII.GraphConjecture84.path_support_subset_maximal_core
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:36:16.965668+00:00
-- url     : https://prove2.me/submissions/cf335c8c-1dba-40fc-88cd-c5761c31b00b

module
public import Mathlib
public import Definitions.Def_Wowii84_LargestInducedTree
public import Definitions.Def_Wowii84_Main
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_core_union_path_delete_connected

set_option autoImplicit false
@[expose] public section
public section
open WrittenOnTheWallII WrittenOnTheWallII.GraphConjecture84
open SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α]
namespace WrittenOnTheWallII.GraphConjecture84
theorem _root_.solution {G : SimpleGraph α} (K : Finset α)
    (hcard : 3 ≤ K.card) (hK : (G.induce (K : Set α)).Connected)
    (hdel : ∀ x : ↥(K : Set α),
      ((G.induce (K : Set α)).induce ({x}ᶜ : Set ↥(K : Set α))).Connected)
    (hmax : ∀ t : Finset α, K ⊆ t → 3 ≤ t.card → (G.induce (t : Set α)).Connected →
      (∀ x : ↥(t : Set α),
        ((G.induce (t : Set α)).induce ({x}ᶜ : Set ↥(t : Set α))).Connected) → t = K)
    {a b : α} (ha : a ∈ K) (hb : b ∈ K) (hab : a ≠ b)
    (p : G.Walk a b) (hp : p.IsPath) : ∀ z ∈ p.support, z ∈ K := by
  classical
  let U := K ∪ p.support.toFinset
  have hsubset : K ⊆ U := Finset.subset_union_left
  have hUcard : 3 ≤ U.card := hcard.trans (Finset.card_le_card hsubset)
  have hUconn : (G.induce (U : Set α)).Connected := by
    have hset : (U : Set α) = (K : Set α) ∪ {z | z ∈ p.support} := by
      ext z
      simp [U]
    rw [hset]
    exact induce_union_connected hK.preconnected p.connected_induce_support.preconnected
      ⟨a, ha, p.start_mem_support⟩
  have hUeq := hmax U hsubset hUcard hUconn
    (core_union_path_delete_connected K hcard hK hdel ha hb hab p hp)
  intro z hz
  have hzU : z ∈ U := Finset.mem_union_right _ (List.mem_toFinset.mpr hz)
  exact hUeq ▸ hzU
end WrittenOnTheWallII.GraphConjecture84
