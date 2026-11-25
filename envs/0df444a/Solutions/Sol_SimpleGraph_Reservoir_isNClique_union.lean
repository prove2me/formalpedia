-- Prove2me | solution 1 for SimpleGraph.Reservoir.isNClique_union
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:27:55.699269+00:00
-- url     : https://prove2.me/submissions/06460da7-1955-4607-bf92-45633c2578c2

module
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Definitions.Def_RamseyReservoir_Reservoir
public import Theorems.Thm_SimpleGraph_IsClique_union_of_forall_adj

set_option autoImplicit true
@[expose] public section
public section
open Finset
open SimpleGraph
variable {V : Type*} (G : SimpleGraph V)
open SimpleGraph.Reservoir
variable {G}
variable (R : G.Reservoir)
namespace SimpleGraph.Reservoir
theorem _root_.solution [DecidableEq V] {t : Finset V} {n : ℕ} (ht : G.IsNClique n t)
    (hsub : t ⊆ R.pool) : G.IsNClique (#R.spine + n) (R.spine ∪ t) := by
  refine ⟨?_, ?_⟩
  · rw [coe_union]
    exact R.isClique_spine.union_of_forall_adj ht.isClique fun x hx y hy => R.adj x hx y (hsub hy)
  · rw [card_union_of_disjoint (R.disjoint.mono_right hsub), ht.card_eq]
end SimpleGraph.Reservoir
