-- Prove2me | solution 1 for SimpleGraph.degreeWithin_univ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:30:54.932379+00:00
-- url     : https://prove2.me/submissions/7677dcb3-0ca2-4e16-b1f3-5e82a0486256

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

set_option autoImplicit true
@[expose] public section
public section
open Finset
open SimpleGraph
variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
omit [DecidableEq V]
namespace SimpleGraph
theorem _root_.solution [Fintype V] (v : V) : G.degreeWithin univ v = G.degree v := by
  rw [degreeWithin, ← card_neighborFinset_eq_degree, neighborFinset_eq_filter]
end SimpleGraph
