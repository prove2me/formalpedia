-- Prove2me | solution 1 for SimpleGraph.indicator_nonconstant_eq_one_or_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:56:05.206884+00:00
-- url     : https://prove2.me/submissions/596ef86f-e76d-4cdc-9b66-d00631b529c8

module
public import Definitions.Def_ChromaticPolynomial_SpanningSubgraph
public import Definitions.Def_ChromaticPolynomial_ConstantOnConnectedComponents
public import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Data.Sym.Sym2
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Logic.Equiv.Set
public import Definitions.Def_ChromaticPolynomial_ChromaticPolynomial

set_option autoImplicit true
@[expose] public section
public section
universe u
open SimpleGraph
variable {V : Type u} [Fintype V] (G : SimpleGraph V)
open Classical
variable (R: Type*) [CommRing R] [CharZero R] [NoZeroDivisors R]
variable (α : Type*) [Fintype α]
variable (e : Sym2 V)
omit [Fintype V] [NoZeroDivisors R] [Fintype α]
namespace SimpleGraph
theorem _root_.solution (π : V → α) :
  indicator_nonconstant R α π e = 1 ∨ indicator_nonconstant R α π e = 0 := by
    obtain ⟨⟨v, w⟩, hvw⟩ := e.exists_rep
    simp [indicator_nonconstant, ← hvw]
    exact ne_or_eq (π v) (π w)
end SimpleGraph
