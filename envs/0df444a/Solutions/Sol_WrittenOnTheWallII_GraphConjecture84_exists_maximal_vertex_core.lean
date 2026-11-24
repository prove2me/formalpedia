-- Prove2me | solution 1 for WrittenOnTheWallII.GraphConjecture84.exists_maximal_vertex_core
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:36:29.176942+00:00
-- url     : https://prove2.me/submissions/18dde09f-3570-4399-a5f1-15cd89e9e7c8

module
public import Mathlib
public import Definitions.Def_Wowii84_LargestInducedTree
public import Definitions.Def_Wowii84_Main
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_cycle_support_delete_connected

set_option autoImplicit false
@[expose] public section
public section
open WrittenOnTheWallII WrittenOnTheWallII.GraphConjecture84
open SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α]
namespace WrittenOnTheWallII.GraphConjecture84
theorem _root_.solution {G : SimpleGraph α} (hcyc : ¬ G.IsAcyclic) :
    ∃ s : Finset α, 3 ≤ s.card ∧ (G.induce (s : Set α)).Connected ∧
      (∀ x : ↥(s : Set α),
        ((G.induce (s : Set α)).induce ({x}ᶜ : Set ↥(s : Set α))).Connected) ∧
      ∀ t : Finset α, s ⊆ t → 3 ≤ t.card → (G.induce (t : Set α)).Connected →
        (∀ x : ↥(t : Set α),
          ((G.induce (t : Set α)).induce ({x}ᶜ : Set ↥(t : Set α))).Connected) → t = s := by
  classical
  obtain ⟨v, p, hp, _⟩ := G.exists_girth_eq_length.mpr hcyc
  have hcardtail : p.support.tail.toFinset.card = p.length := by
    rw [List.toFinset_card_of_nodup hp.support_nodup, List.length_tail, p.length_support]
    omega
  have hcard : 3 ≤ p.support.toFinset.card := by
    have hle : p.support.tail.toFinset.card ≤ p.support.toFinset.card := by
      apply Finset.card_le_card
      intro z hz
      exact List.mem_toFinset.mpr (List.mem_of_mem_tail (List.mem_toFinset.mp hz))
    have hthree := hp.three_le_length
    omega
  let A : Set (Finset α) := {s | 3 ≤ s.card ∧ (G.induce (s : Set α)).Connected ∧
    ∀ x : ↥(s : Set α),
      ((G.induce (s : Set α)).induce ({x}ᶜ : Set ↥(s : Set α))).Connected}
  have hA : A.Nonempty := by
    refine ⟨p.support.toFinset, hcard, ?_, cycle_support_delete_connected p hp⟩
    have hset : (p.support.toFinset : Set α) = {z | z ∈ p.support} := by ext z; simp
    rw [hset]
    exact p.connected_induce_support
  obtain ⟨s, hs, hmax⟩ := Set.exists_max_image A Finset.card (Set.toFinite A) hA
  refine ⟨s, hs.1, hs.2.1, hs.2.2, ?_⟩
  intro t hst htcard htconn htdel
  symm
  apply Finset.eq_of_subset_of_card_le hst
  exact hmax t ⟨htcard, htconn, htdel⟩
end WrittenOnTheWallII.GraphConjecture84
