-- Prove2me | solution 1 for SimpleGraph.indicator_proper_eq_one_or_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:57:10.099664+00:00
-- url     : https://prove2.me/submissions/84163f12-dab2-4a4e-a12b-937c92eec57a

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
public import Theorems.Thm_SimpleGraph_indicator_nonconstant_eq_one_or_zero

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
omit [NoZeroDivisors R] [Fintype α]
namespace SimpleGraph
theorem _root_.solution (π : V → α) :
  G.indicator_proper R α π = 1 ∨ G.indicator_proper R α π = 0 := by
    by_cases h : ∃ e ∈ G.edgeSet, indicator_nonconstant R α π e = 0
    right
    obtain ⟨e₀, ⟨he₀, idxe₀⟩⟩ := h
    simp
    calc ∏ e ∈ G.edgeSet.toFinset, indicator_nonconstant R α π e =
      indicator_nonconstant R α π e₀ *  ∏ e ∈ G.edgeSet.toFinset \ {e₀}, indicator_nonconstant R α π e := by
          refine Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (f := indicator_nonconstant R α π) ?h
          exact mem_edgeFinset.mpr he₀
      _ = 0 := by
          rw [idxe₀]
          simp
    left
    apply Finset.prod_eq_one
    intro e he
    let e₁ : G.edgeSet := ⟨e, Set.mem_toFinset.mp he⟩
    apply (Or.resolve_right (indicator_nonconstant_eq_one_or_zero R α e₁ π))
    simp at h
    apply h
    exact mem_edgeFinset.mp he
end SimpleGraph
