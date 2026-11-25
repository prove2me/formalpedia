-- Prove2me | solution 1 for SimpleGraph.RamseyBound.mono_sizes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:34:33.051802+00:00
-- url     : https://prove2.me/submissions/3c21208d-8dd1-49e2-bedc-871119669179

module
public import Definitions.Def_RamseyReservoir_RamseyBound
public import Definitions.Def_RamseyReservoir_Reservoir
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Combinatorics.SimpleGraph.Circulant
public import Definitions.Def_RamseyReservoir_Bireservoir
public import Theorems.Thm_SimpleGraph_IsClique_exists_isNClique_subset
public import Theorems.Thm_SimpleGraph_RamseyBound_exists_isNClique_subset


set_option autoImplicit true
@[expose] public section
public section
open Finset
open SimpleGraph
variable {V : Type*} (G : SimpleGraph V)
open SimpleGraph.Bireservoir
variable {G}
variable (S : G.Bireservoir)
namespace SimpleGraph.Bireservoir
namespace _root_.SimpleGraph.RamseyBound
theorem _root_.solution {n r s r' s' : ℕ} (h : RamseyBound n r s)
    (hr : r' ≤ r) (hs : s' ≤ s) : RamseyBound n r' s' := fun H => by
  rcases h H with ⟨t, ht⟩ | ⟨t, ht⟩
  · obtain ⟨u, -, hu⟩ := ht.isClique.exists_isNClique_subset (ht.card_eq ▸ hr)
    exact .inl ⟨u, hu⟩
  · obtain ⟨u, -, hu⟩ := ht.isClique.exists_isNClique_subset (ht.card_eq ▸ hs)
    exact .inr ⟨u, hu⟩
end _root_.SimpleGraph.RamseyBound
end SimpleGraph.Bireservoir
