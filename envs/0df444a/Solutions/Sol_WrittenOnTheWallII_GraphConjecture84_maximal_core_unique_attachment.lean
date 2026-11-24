-- Prove2me | solution 1 for WrittenOnTheWallII.GraphConjecture84.maximal_core_unique_attachment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:37:47.333198+00:00
-- url     : https://prove2.me/submissions/138c7287-71bf-4c57-ad9b-b556a6e0ef50

module
public import Mathlib
public import Definitions.Def_Wowii84_LargestInducedTree
public import Definitions.Def_Wowii84_Main
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_path_support_subset_maximal_core

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
    (z w : ↥((K : Set α)ᶜ)) (hr : (G.induce (K : Set α)ᶜ).Reachable z w)
    {a b : α} (ha : a ∈ K) (hb : b ∈ K) (haz : G.Adj a z) (hbw : G.Adj b w) : a = b := by
  classical
  by_contra hab
  obtain ⟨q, hq, _⟩ := hr.exists_path_of_dist
  let e : G.induce (K : Set α)ᶜ ↪g G := SimpleGraph.Embedding.induce _
  let p : G.Walk (z : α) (w : α) := q.map e.toHom
  have hp : p.IsPath := (Walk.isPath_map_iff_of_injective e.injective).mpr hq
  have hout : ∀ v ∈ p.support, v ∉ K := by
    intro v hv
    change v ∈ (q.map e.toHom).support at hv
    rw [Walk.support_map] at hv
    obtain ⟨v', _, rfl⟩ := List.mem_map.mp hv
    exact v'.property
  have hanot : a ∉ p.support := fun ha' => hout a ha' ha
  have hbnot : b ∉ p.support := fun hb' => hout b hb' hb
  let p' := p.cons haz
  have hp' : p'.IsPath := hp.cons hanot
  have hbnot' : b ∉ p'.support := by
    intro hmem
    have hmem' : b = a ∨ b ∈ p.support := by
      simpa only [p', Walk.support_cons, List.mem_cons] using hmem
    exact hmem'.elim (fun heq => hab heq.symm) hbnot
  let p'' := p'.concat hbw.symm
  have hp'' : p''.IsPath := hp'.concat hbnot' hbw.symm
  have hsub := path_support_subset_maximal_core K hcard hK hdel hmax ha hb hab p'' hp''
  have hzmem : (z : α) ∈ p''.support := by
    apply p'.support_subset_support_concat hbw.symm
    change (z : α) ∈ (p.cons haz).support
    simp only [Walk.support_cons, List.mem_cons]
    have hz0 := p.start_mem_support
    change (z : α) ∈ p.support at hz0
    exact Or.inr hz0
  exact z.property (hsub z hzmem)
end WrittenOnTheWallII.GraphConjecture84
