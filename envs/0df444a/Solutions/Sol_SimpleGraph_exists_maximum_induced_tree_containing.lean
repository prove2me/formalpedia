-- Prove2me | solution 1 for SimpleGraph.exists_maximum_induced_tree_containing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:26:03.323829+00:00
-- url     : https://prove2.me/submissions/441490b8-9fc8-4919-9aef-8b6936bbcfac

module
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Girth
public import Mathlib.Data.Set.Finite.Lemmas
public import Definitions.Def_Wowii84_LargestInducedTree

set_option autoImplicit false
@[expose] public section
public section
open SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α]
omit [DecidableEq α]
namespace SimpleGraph
theorem _root_.solution (G : SimpleGraph α) (r : Finset α)
    (hr : ∃ s : Finset α, r ⊆ s ∧ (G.induce (s : Set α)).IsTree) :
    ∃ s : Finset α,
      r ⊆ s ∧
      (G.induce (s : Set α)).IsTree ∧
      ∀ t : Finset α, r ⊆ t →
        (G.induce (t : Set α)).IsTree → t.card ≤ s.card := by
  let A : Set (Finset α) :=
    {s | r ⊆ s ∧ (G.induce (s : Set α)).IsTree}
  have hAfin : A.Finite := Set.toFinite A
  have hAne : A.Nonempty := by
    obtain ⟨s, hrs, hT⟩ := hr
    exact ⟨s, hrs, hT⟩
  obtain ⟨s, hsA, hmax⟩ := Set.exists_max_image A Finset.card hAfin hAne
  dsimp [A] at hsA hmax
  refine ⟨s, hsA.1, hsA.2, ?_⟩
  intro t hrt hT
  exact hmax t ⟨hrt, hT⟩
end SimpleGraph
