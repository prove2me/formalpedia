-- Prove2me | solution 1 for SimpleGraph.two_le_card_cliqueFinset_add_card_cliqueFinset_compl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:59:49.394086+00:00
-- url     : https://prove2.me/submissions/a85c044b-a01e-47a3-9894-0ba3888cc2cc

module
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Zify
public import Definitions.Def_GoodmanSupersaturation_Goodman
public import Theorems.Thm_SimpleGraph_goodman_bound

set_option autoImplicit true
@[expose] public section
public section
open Finset
open SimpleGraph
variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable [Fintype V]
namespace SimpleGraph
theorem _root_.solution (h6 : Fintype.card V = 6) :
    2 ≤ #(G.cliqueFinset 3) + #(Gᶜ.cliqueFinset 3) := by
  have := goodman_bound G
  rw [h6] at this
  omega
end SimpleGraph
