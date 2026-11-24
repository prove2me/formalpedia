-- Prove2me | solution 1 for WrittenOnTheWallII.GraphConjecture84.shallow_geodesic_meets_core
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:34:07.965077+00:00
-- url     : https://prove2.me/submissions/76a4e38f-4fed-40ac-b5e3-9cd8425eed92

module
public import Mathlib
public import Definitions.Def_Wowii84_LargestInducedTree
public import Definitions.Def_Wowii84_Main
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_reachable_compl_of_mem_geodesic
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_exists_two_adj_of_connected_deletions
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_adjacent_start_eq_snd_of_geodesic
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_core_reachable_compl

set_option autoImplicit false
@[expose] public section
public section
open WrittenOnTheWallII WrittenOnTheWallII.GraphConjecture84
open SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α]
namespace WrittenOnTheWallII.GraphConjecture84
theorem _root_.solution {G : SimpleGraph α} (hG : G.Connected)
    (K : Finset α) (hcard : 3 ≤ K.card) (hK : (G.induce (K : Set α)).Connected)
    (hdel : ∀ x : ↥(K : Set α),
      ((G.induce (K : Set α)).induce ({x}ᶜ : Set ↥(K : Set α))).Connected)
    (c : α) (hc : c ∈ K) (a b : ↥({c}ᶜ : Set α))
    (q : G.Walk c (b : α)) (hq : q.length = G.dist c b)
    (hsep : ¬ (G.induce ({c}ᶜ : Set α)).Reachable a b)
    (hcover : ∀ z, z ∈ cutSide G c a ∨ z ∈ q.support) :
    (∀ z ∈ K, z ∈ cutSide G c a) ∧ (∀ z ∈ q.support, z ∈ K → z = c) := by
  classical
  obtain ⟨u, v, hcu, hcv, huv⟩ := exists_two_adj_of_connected_deletions
    (G := G.induce (K : Set α)) (by simpa using hcard) hK hdel ⟨c, hc⟩
  have hside : ∀ z ∈ K, z ∈ cutSide G c a := by
    intro z hz
    by_contra hzside
    have hzc : z ≠ c := fun heq => hzside (Or.inl heq)
    have hneighbor (w : ↥(K : Set α)) (hcw : G.Adj c w) : (w : α) = q.snd := by
      have hwc := hcw.ne.symm
      have hzw := core_reachable_compl K hK hdel c hz w.property hzc hwc
      have hwnot : (w : α) ∉ cutSide G c a := by
        rintro (hwc' | ⟨_, haw⟩)
        · exact hwc hwc'
        · exact hzside (Or.inr ⟨hzc, haw.trans hzw.symm⟩)
      exact adjacent_start_eq_snd_of_geodesic hG q hq
        ((hcover w).resolve_left hwnot) hcw
    have huq := hneighbor u hcu
    have hvq := hneighbor v hcv
    exact huv (Subtype.ext (huq.trans hvq.symm))
  refine ⟨hside, ?_⟩
  intro z hzq hzK
  by_contra hzc
  have hzb := reachable_compl_of_mem_geodesic q hq b.property hzq hzc
  rcases hside z hzK with heq | ⟨_, haz⟩
  · exact hzc heq
  · exact hsep (haz.trans hzb)
end WrittenOnTheWallII.GraphConjecture84
