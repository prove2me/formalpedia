-- Prove2me | solution 1 for WrittenOnTheWallII.GraphConjecture84.exists_walk_in_core_avoiding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:24:35.611825+00:00
-- url     : https://prove2.me/submissions/eb13bbe6-5536-4cd5-ad8c-d0565bd092d9

module
public import Mathlib
public import Definitions.Def_Wowii84_LargestInducedTree
public import Definitions.Def_Wowii84_Main

set_option autoImplicit false
@[expose] public section
public section
open WrittenOnTheWallII WrittenOnTheWallII.GraphConjecture84
open SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α]
namespace WrittenOnTheWallII.GraphConjecture84
theorem _root_.solution {G : SimpleGraph α} (K : Finset α)
    (hK : (G.induce (K : Set α)).Connected)
    (hdel : ∀ x : ↥(K : Set α),
      ((G.induce (K : Set α)).induce ({x}ᶜ : Set ↥(K : Set α))).Connected)
    (x : α) {u v : α} (hu : u ∈ K) (hv : v ∈ K) (hux : u ≠ x) (hvx : v ≠ x) :
    ∃ p : G.Walk u v, (∀ z ∈ p.support, z ∈ K) ∧ x ∉ p.support := by
  classical
  by_cases hx : x ∈ K
  · let x' : ↥(K : Set α) := ⟨x, hx⟩
    let u' : ↥({x'}ᶜ : Set ↥(K : Set α)) := ⟨⟨u, hu⟩, by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro heq
      exact hux (congrArg Subtype.val heq)⟩
    let v' : ↥({x'}ᶜ : Set ↥(K : Set α)) := ⟨⟨v, hv⟩, by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro heq
      exact hvx (congrArg Subtype.val heq)⟩
    obtain ⟨p⟩ := hdel x' u' v'
    let f : (G.induce (K : Set α)).induce ({x'}ᶜ : Set ↥(K : Set α)) →g G :=
      { toFun := fun z => ((z : ↥(K : Set α)) : α)
        map_rel' := by intro u v huv; exact huv }
    refine ⟨p.map f, ?_, ?_⟩
    · intro z hz
      rw [Walk.support_map] at hz
      obtain ⟨w, _, rfl⟩ := List.mem_map.mp hz
      exact (w : ↥(K : Set α)).property
    · intro hxmem
      rw [Walk.support_map] at hxmem
      obtain ⟨w, _, hw⟩ := List.mem_map.mp hxmem
      have hwne : (w : ↥(K : Set α)) ≠ x' := w.property
      exact hwne (Subtype.ext hw)
  · obtain ⟨p⟩ := hK (⟨u, hu⟩ : ↥(K : Set α)) ⟨v, hv⟩
    let f : G.induce (K : Set α) →g G := (SimpleGraph.Embedding.induce (K : Set α)).toHom
    have hsub : ∀ z ∈ (p.map f).support, z ∈ K := by
      intro z hz
      rw [Walk.support_map] at hz
      obtain ⟨w, _, rfl⟩ := List.mem_map.mp hz
      exact w.property
    exact ⟨p.map f, hsub, fun hxmem => hx (hsub x hxmem)⟩
end WrittenOnTheWallII.GraphConjecture84
