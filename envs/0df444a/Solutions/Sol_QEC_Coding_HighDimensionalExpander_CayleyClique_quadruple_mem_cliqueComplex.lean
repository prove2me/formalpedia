-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CayleyClique.quadruple_mem_cliqueComplex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:05:50.717237+00:00
-- url     : https://prove2.me/submissions/b04d2077-2e48-4c57-aa35-f5582b3be1f9

import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
import Mathlib.Combinatorics.SimpleGraph.Cayley
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_CayleyClique
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CayleyClique_triple_mem_cliqueComplex

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CayleyClique
open Finset
universe u v
variable {V : Type u} {W : Type v}
namespace QEC.Coding.HighDimensionalExpander.CayleyClique
theorem _root_.solution
    [DecidableEq V] (G : SimpleGraph V) {a b c d : V}
    (hab : G.Adj a b) (hac : G.Adj a c) (had : G.Adj a d)
    (hbc : G.Adj b c) (hbd : G.Adj b d) (hcd : G.Adj c d) :
    {a, b, c, d} ∈ cliqueComplex G := by
  rw [mem_cliqueComplex_iff]
  refine ⟨by simp, ?_⟩
  have habc : G.IsClique ({a, b, c} : Set V) := by
    have hmem := triple_mem_cliqueComplex G hab hac hbc
    have hfin := (mem_cliqueComplex_iff G {a, b, c}).mp hmem |>.2
    simpa only [Finset.coe_insert, Finset.coe_singleton] using hfin
  have hins : G.IsClique (insert d ({a, b, c} : Set V)) :=
    habc.insert (by
      intro x hx _
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact G.adj_symm had
      · exact G.adj_symm hbd
      · exact G.adj_symm hcd)
  have hset :
      (({a, b, c, d} : Finset V) : Set V) =
        insert d ({a, b, c} : Set V) := by
    ext x
    simp only [Finset.coe_insert, Finset.coe_singleton,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  rw [hset]
  exact hins
end QEC.Coding.HighDimensionalExpander.CayleyClique
