-- Prove2me | solution 1 for SimpleGraph.indicator_proper_eq_one_iff_proper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:56:12.851934+00:00
-- url     : https://prove2.me/submissions/3f7c9d1b-4495-4842-ae10-5e83615f4e2d

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
omit [NoZeroDivisors R] [Fintype α]
namespace SimpleGraph
theorem _root_.solution (π : V → α) :
  (G.indicator_proper R α π) = 1 ↔ G.is_proper α π := by
    constructor
    · intro h v w hedge
      contrapose h
      let e₀ := s(v, w)
      let f := indicator_nonconstant R α π
      have h₁ : f e₀ = 0 := by
        simp only [f, e₀, h, indicator_nonconstant, Sym2.lift_mk]
        simp
      simp
      apply Ne.symm
      calc 1 ≠ 0 := one_ne_zero
      _ = indicator_nonconstant R α π e₀ * ∏ e ∈ G.edgeSet.toFinset \ {e₀}, indicator_nonconstant R α π e := by
        simp_all only [zero_mul, f, e₀]
      _ = ∏ e ∈ G.edgeSet.toFinset, indicator_nonconstant R α π e := by
          refine Eq.symm (Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (f := indicator_nonconstant R α π) ?h)
          exact mem_edgeFinset.mpr hedge
    · intro h
      simp
      rw [Finset.prod_eq_one]
      intro e he
      simp [Set.mem_toFinset] at he
      obtain ⟨⟨v, w⟩, hsw⟩ := e.exists_rep
      simp [indicator_nonconstant]
      rw [← hsw]
      simp [Sym2.lift_mk]
      subst hsw
      exact h he
end SimpleGraph
