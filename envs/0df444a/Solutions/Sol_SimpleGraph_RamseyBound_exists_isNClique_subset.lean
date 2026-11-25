-- Prove2me | solution 1 for SimpleGraph.RamseyBound.exists_isNClique_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:25:52.379652+00:00
-- url     : https://prove2.me/submissions/ebb1dd48-e3ae-42f4-a632-dfe5baf29bd3

module
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Definitions.Def_RamseyReservoir_RamseyBound
section
@[expose] public section
open Finset
namespace SimpleGraph
variable {V : Type*} {n m r s : ℕ}
private theorem compl_comap_embedding (G : SimpleGraph V) (f : Fin n ↪ V) :
    (G.comap f)ᶜ = Gᶜ.comap f := by
  ext a b
  simp [f.injective.ne_iff]
private theorem isNClique_map_of_comap {G : SimpleGraph V} {f : Fin n ↪ V} {k : ℕ}
    {t : Finset (Fin n)} (ht : (G.comap f).IsNClique k t) : G.IsNClique k (t.map f) := by
  have := ht.map (f := f)
  exact this.mono (map_comap_le _ _)
end SimpleGraph
end
end

set_option autoImplicit true
@[expose] public section
public section
open Finset
open SimpleGraph
variable {V : Type*} {n m r s : ℕ}
namespace SimpleGraph
namespace RamseyBound
theorem _root_.solution (h : RamseyBound n r s) (G : SimpleGraph V)
    {X : Finset V} (hX : n ≤ #X) :
    (∃ t ⊆ X, G.IsNClique r t) ∨ ∃ t ⊆ X, Gᶜ.IsNClique s t := by
  classical
  obtain ⟨Y, hYX, hY⟩ := exists_subset_card_eq hX
  let e : Fin n ↪ V := ⟨fun i => (Y.equivFin.symm (Fin.cast hY.symm i) : V),
    fun i j hij => by simpa using Subtype.ext hij⟩
  have he : ∀ t : Finset (Fin n), t.map e ⊆ X := fun t x hx => by
    obtain ⟨i, -, rfl⟩ := mem_map.mp hx
    exact hYX (Y.equivFin.symm _).2
  rcases h (G.comap e) with ⟨t, ht⟩ | ⟨t, ht⟩
  · exact .inl ⟨_, he t, isNClique_map_of_comap ht⟩
  · rw [compl_comap_embedding] at ht
    exact .inr ⟨_, he t, isNClique_map_of_comap ht⟩
end RamseyBound
end SimpleGraph
