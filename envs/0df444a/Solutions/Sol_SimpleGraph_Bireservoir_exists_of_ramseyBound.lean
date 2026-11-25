-- Prove2me | solution 1 for SimpleGraph.Bireservoir.exists_of_ramseyBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:31:47.808361+00:00
-- url     : https://prove2.me/submissions/0a2af2ce-4472-462b-8efe-638d89434111

module
public import Definitions.Def_RamseyReservoir_RamseyBound
public import Definitions.Def_RamseyReservoir_Reservoir
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Combinatorics.SimpleGraph.Circulant
public import Definitions.Def_RamseyReservoir_Bireservoir
public import Theorems.Thm_SimpleGraph_Bireservoir_toRed_spine
public import Theorems.Thm_SimpleGraph_Bireservoir_toBlue_spine
public import Theorems.Thm_SimpleGraph_IsClique_exists_isNClique_subset
public import Theorems.Thm_SimpleGraph_RamseyBound_exists_isNClique_subset
public import Theorems.Thm_SimpleGraph_Reservoir_isNClique_union
public import Theorems.Thm_SimpleGraph_Reservoir_ofPool_pool
public import Theorems.Thm_SimpleGraph_Reservoir_ofPool_spine
public import Theorems.Thm_SimpleGraph_Reservoir_pivot_pool
public import Theorems.Thm_SimpleGraph_Reservoir_pivot_spine
attribute [local simp] SimpleGraph.Reservoir.ofPool_pool
attribute [local simp] SimpleGraph.Reservoir.ofPool_spine
attribute [local simp] SimpleGraph.Reservoir.pivot_pool
attribute [local simp] SimpleGraph.Reservoir.pivot_spine


attribute [local simp] SimpleGraph.Bireservoir.toRed_spine
attribute [local simp] SimpleGraph.Bireservoir.toBlue_spine

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
theorem _root_.solution {n r s : ℕ} (h : RamseyBound n (r - #S.red) (s - #S.blue))
    (hn : n ≤ #S.pool) : (∃ t, G.IsNClique r t) ∨ ∃ t, Gᶜ.IsNClique s t := by
  classical
  rcases h.exists_isNClique_subset G hn with ⟨t, ht, hc⟩ | ⟨t, ht, hc⟩
  · have hu := S.toRed.isNClique_union hc ht
    obtain ⟨u, -, hu⟩ := hu.isClique.exists_isNClique_subset (r := r) (by
      rw [hu.card_eq, toRed_spine]; omega)
    exact .inl ⟨u, hu⟩
  · have hu := S.toBlue.isNClique_union hc ht
    obtain ⟨u, -, hu⟩ := hu.isClique.exists_isNClique_subset (r := s) (by
      rw [hu.card_eq, toBlue_spine]; omega)
    exact .inr ⟨u, hu⟩
end SimpleGraph.Bireservoir
