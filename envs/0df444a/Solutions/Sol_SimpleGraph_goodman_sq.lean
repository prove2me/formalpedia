-- Prove2me | solution 1 for SimpleGraph.goodman_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:52:50.214655+00:00
-- url     : https://prove2.me/submissions/4cca3e8f-297c-47de-8d82-ccce73e51058

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
public import Theorems.Thm_SimpleGraph_degreeWithin_univ
public import Theorems.Thm_SimpleGraph_cliqueCountIn_univ
public import Theorems.Thm_SimpleGraph_goodman_sq_within
attribute [local simp] SimpleGraph.degreeWithin_univ
attribute [local simp] SimpleGraph.cliqueCountIn_univ

set_option autoImplicit true
@[expose] public section
public section
open Finset
open SimpleGraph
variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable [Fintype V]
namespace SimpleGraph
theorem _root_.solution :
    8 * ((#(G.cliqueFinset 3) + #(Gᶜ.cliqueFinset 3) : ℕ) : ℤ) +
        Fintype.card V * ((Fintype.card V : ℤ) - 1) ^ 2 =
      8 * (Fintype.card V).choose 3 + ∑ v, ((G.degree v : ℤ) - Gᶜ.degree v) ^ 2 := by
  simpa using goodman_sq_within G univ
end SimpleGraph
