-- Prove2me | solution 1 for SimpleGraph.Reservoir.not_isNClique_of_cliqueFree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:33:23.024174+00:00
-- url     : https://prove2.me/submissions/09896f02-12d4-4a3c-a167-b4e2558ca7ac

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
theorem _root_.solution {n : ℕ} (hG : G.CliqueFree (#R.spine + n)) {t : Finset V}
    (hsub : t ⊆ R.pool) : ¬G.IsNClique n t := by
  classical
  exact fun ht => hG _ (R.isNClique_union ht hsub)
end SimpleGraph.Reservoir
