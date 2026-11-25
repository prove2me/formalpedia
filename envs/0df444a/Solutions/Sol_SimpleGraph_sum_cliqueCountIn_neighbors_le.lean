-- Prove2me | solution 1 for SimpleGraph.sum_cliqueCountIn_neighbors_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:53:13.298939+00:00
-- url     : https://prove2.me/submissions/dae29d50-0bcf-46e1-b8be-7147199da5d0

module
public import Definitions.Def_GoodmanSupersaturation_Goodman
public import Mathlib.Tactic.Rify
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Definitions.Def_GoodmanSupersaturation_Supersaturation
public import Theorems.Thm_SimpleGraph_sum_cliqueCountIn_neighbors_eq

set_option autoImplicit true
@[expose] public section
public section
open Finset
open SimpleGraph
variable {V : Type*}
variable [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
namespace SimpleGraph
theorem _root_.solution (S : Finset V) {j : ℕ} (hj : 1 ≤ j) :
    ∑ v ∈ S, G.cliqueCountIn {w ∈ S | G.Adj v w} (j - 1) ≤ j * G.cliqueCountIn S j :=
  (sum_cliqueCountIn_neighbors_eq G S hj).le
end SimpleGraph
