-- Prove2me | solution 1 for SimpleGraph.indicator_constant_connected_components
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:57:10.578218+00:00
-- url     : https://prove2.me/submissions/695020fe-4f88-4675-903f-10a5b5291fd4

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
public import Theorems.Thm_SimpleGraph_indicator_constant_eq_one_or_zero

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
open Finset
namespace SimpleGraph
theorem _root_.solution (F :  {F // F ⊆ G.edgeSet}) : ∑ (π : V → α), ∏ (e ∈ F.val), (indicator_constant R α π e) =
  (↑(Fintype.card α))^(G.edge_subset_ConnectedComponent_card F) := by
    let H := (G.spanningSubgraph_fromEdgeSet' F)
    have h' : H.edgeSet = ↑F := by
                simp [H]
                change (fromEdgeSet F).edgeSet = F.val
                rw [edgeSet_fromEdgeSet]
                exact (powerset_edgeSet_eq_diff_setOf_isDiag G F).symm
    calc ∑ π : V → α, ∏ (e ∈ F.val), indicator_constant R α π e =
      ∑ π : V → α, ite (∀ e ∈ F.val, indicator_constant R α π e = 1) 1 0 := by
          apply sum_congr rfl; intro π _
          by_cases h : ∀ e ∈ F.val, indicator_constant R α π e = 1
          · simp_all [prod_eq_one]
          · apply eq_ite_iff.mpr
            right
            constructor
            · exact h
            · apply prod_eq_zero_iff.mpr
              simp at h
              obtain ⟨e, he, hzero⟩ := h
              use e
              constructor
              simp [he]
              exact Or.resolve_left (indicator_constant_eq_one_or_zero R α e π) hzero
      _ = ∑ π : V → α, ite (∀ {v w : V}, H.Adj v w → π v = π w) 1 0 := by
          apply sum_congr rfl; intro π _
          apply ite_congr
          · rw [eq_iff_iff]
            apply Iff.intro
            · intro hone v w hvw
              simp [Sym2.forall, indicator_constant] at hone
              apply hone
              rw [← H.mem_edgeSet] at hvw
              rw [← h']
              exact hvw
            · intro hallvw e he
              simp [indicator_constant]
              obtain ⟨⟨v, w⟩, hsw⟩ := e.exists_rep
              rw [← hsw]
              simp [Sym2.lift_mk]
              apply hallvw
              rw [← H.mem_edgeSet, h']
              exact Set.mem_of_eq_of_mem hsw he
          repeat' exact fun _ ↦ rfl
      _ = Fintype.card {π : V → α //  ∀ {v w : V}, H.Adj v w → π v = π w} := by
          rw [sum_ite, sum_const_zero, add_zero, sum_const]
          simp
          symm
          apply Fintype.card_subtype
      _ = Fintype.card (H.coe.ConnectedComponent → α) := by
          apply Nat.cast_inj.mpr
          apply Fintype.card_congr
          symm
          apply Equiv.trans (Equiv.symm (H.coe).equiv_constant_on_cc)
          apply Equiv.subtypeEquiv (Equiv.arrowCongr (Equiv.Set.univ V) (Equiv.refl α))
          intro _
          constructor
          repeat'
          intro h _ _ hadj
          exact h hadj
      _ = (↑(Fintype.card α))^(G.edge_subset_ConnectedComponent_card F) := by
          simp
          exact rfl
end SimpleGraph
