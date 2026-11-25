-- Prove2me | solution 1 for SimpleGraph.Reservoir.exists_isNClique_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:30:58.346796+00:00
-- url     : https://prove2.me/submissions/1022fb24-34b5-4ae9-bed5-2ab5803f7921

module
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Definitions.Def_RamseyReservoir_Reservoir
public import Theorems.Thm_SimpleGraph_Reservoir_isNClique_union

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
theorem _root_.solution (hR : R.pool.Nonempty) :
    ∃ s, G.IsNClique (#R.spine + 1) s := by
  classical
  obtain ⟨v, hv⟩ := hR
  exact ⟨_, R.isNClique_union (isNClique_singleton.mpr rfl) (singleton_subset_iff.mpr hv)⟩
end SimpleGraph.Reservoir
