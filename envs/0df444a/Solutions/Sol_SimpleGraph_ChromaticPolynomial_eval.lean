-- Prove2me | solution 1 for SimpleGraph.ChromaticPolynomial_eval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:57:45.829508+00:00
-- url     : https://prove2.me/submissions/ac09f194-4b57-4aee-9b60-2fe48486cf4d

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
public import Theorems.Thm_SimpleGraph_indicator_nonconstant_eq_one_minus_indicator_constant
public import Theorems.Thm_SimpleGraph_indicator_proper_eq_one_or_zero
public import Theorems.Thm_SimpleGraph_indicator_proper_eq_one_iff_proper
public import Theorems.Thm_SimpleGraph_indicator_constant_connected_components

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
theorem _root_.solution (α : Type*) [Fintype α] :
  (G.ChromaticPolynomial R).eval (Fintype.card α : R) = Fintype.card (G.Coloring α) := by
  symm
  let proper := {π : V → α | G.is_proper α π}.toFinset
  let edges :=  G.edgeSet.toFinset
  calc ↑(Fintype.card (G.Coloring α)) = ∑ (_ : (G.Coloring α)), (1:R) := by
         simp [sum_const, card_univ]
    _ = ∑ (_ ∈ proper), (1:R) := by
        simp
        rw [Set.toFinset_card]
        apply Fintype.card_congr (G.coloring_equiv_coloring' α)
    _ = ∑ (π ∈ proper), (G.indicator_proper R α π) := by
        apply sum_congr rfl
        rintro π hproper
        symm
        apply (G.indicator_proper_eq_one_iff_proper R α π).mpr
        exact Set.mem_toFinset.mp hproper
    _ = ∑ (π ∈ proper), (G.indicator_proper R α π) + ∑ (π ∈ properᶜ), (G.indicator_proper R α π) := by
        symm
        apply add_eq_left.mpr
        apply sum_eq_zero
        intro π hnotproper
        rw [← Set.toFinset_compl] at hnotproper
        simp at hnotproper
        rw [← (G.indicator_proper_eq_one_iff_proper R α π)] at hnotproper
        exact Or.resolve_left (G.indicator_proper_eq_one_or_zero R α π) hnotproper
    _ = ∑ (π : V → α), (G.indicator_proper R α π) := by
        exact sum_add_sum_compl proper (G.indicator_proper R α)
    _ = ∑ (π : V → α), ∏ (e ∈ edges), (1 - indicator_constant R α π e) := by
        simp only [indicator_proper]
        apply sum_congr rfl
        intro π _
        apply prod_congr rfl
        intro e he
        rw [Set.mem_toFinset] at he
        apply indicator_nonconstant_eq_one_minus_indicator_constant R α
    _ = ∑ (π : V → α), ∑ (F ∈ G.edgeSet.toFinset.powerset), ∏ (e ∈ F), (-(indicator_constant R α π e)) := by
        simp_rw [sub_eq_add_neg, add_comm (1 : R), Finset.prod_add, Finset.prod_const_one, mul_one]
        rfl
    _ = ∑ (F ∈ G.edgeSet.toFinset.powerset), ∑ (π : V → α), ∏ (e ∈ F), (-(indicator_constant R α π e)) := by
        exact Finset.sum_comm
    _ = ∑ F : {F // F ⊆ G.edgeSet}, ∑ (π : V → α), ∏ (e ∈ F.val), (-(indicator_constant R α π e)) := by
        apply Finset.sum_bij'
          (fun F (hF: F ∈ G.edgeSet.toFinset.powerset) ↦ ⟨(F : Set (Sym2 V)), by {aesop}⟩)
          (fun F _ ↦ F.val.toFinset)
        repeat' simp
    _ = ∑ F : {F // F ⊆ G.edgeSet}, ∑ (π : V → α), ∏ (e ∈ F.val), (-(indicator_constant R α π e)) := by
        apply sum_congr rfl
        simp
    _ = ∑ F : {F // F ⊆ G.edgeSet}, ∑ (π : V → α), ∏ (e ∈ F.val), (-1*(indicator_constant R α π e)) := by
        simp_all only [neg_mul, one_mul]
    _ = ∑ F : {F // F ⊆ G.edgeSet}, ∑ (π : V → α), (-1)^(Fintype.card F) * ∏ (e ∈ F.val), indicator_constant R α π e := by
        simp_rw [Finset.prod_mul_distrib, Finset.prod_const, Set.toFinset_card]
    _ = ∑ F : {F // F ⊆ G.edgeSet},  (-1)^(Fintype.card F) * ∑ (π : V → α), ∏ (e ∈ F.val), indicator_constant R α π e := by
        apply sum_congr rfl; intro F _
        simp [mul_sum]
    _ = ∑ F : {F // F ⊆ G.edgeSet},
      (-1)^(Fintype.card F) * (↑(Fintype.card α))^(G.edge_subset_ConnectedComponent_card F) := by
        apply sum_congr rfl; intro F _
        simp [G.indicator_constant_connected_components R α]
    _ = Polynomial.eval (↑(Fintype.card α)) (G.ChromaticPolynomial R) := by
        dsimp
        rw [Polynomial.eval_finsetSum]
        apply sum_congr rfl; intro F _
        simp
end SimpleGraph
