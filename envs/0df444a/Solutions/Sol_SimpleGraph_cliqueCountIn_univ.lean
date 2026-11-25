-- Prove2me | solution 1 for SimpleGraph.cliqueCountIn_univ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:37:20.275569+00:00
-- url     : https://prove2.me/submissions/6d94ebb1-00cb-4e9f-a4b2-8a842bdd86ed

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
attribute [local simp] SimpleGraph.degreeWithin_univ

set_option autoImplicit true
@[expose] public section
public section
open Finset
open SimpleGraph
variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
namespace SimpleGraph
theorem _root_.solution [Fintype V] (k : ℕ) :
    G.cliqueCountIn univ k = #(G.cliqueFinset k) := by
  rw [cliqueCountIn]
  congr 1
  ext T
  simp [mem_cliqueFinset_iff, isNClique_iff, and_comm]
end SimpleGraph
