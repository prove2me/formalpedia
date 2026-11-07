-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CayleyClique.triple_mem_cliqueComplex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:50:23.333228+00:00
-- url     : https://prove2.me/submissions/5187786b-ce05-4aa7-9948-331237f916ef

import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
import Mathlib.Combinatorics.SimpleGraph.Cayley
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_CayleyClique

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CayleyClique
open Finset
universe u v
variable {V : Type u} {W : Type v}
namespace QEC.Coding.HighDimensionalExpander.CayleyClique
theorem _root_.solution
    [DecidableEq V] (G : SimpleGraph V) {a b c : V}
    (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c) :
    {a, b, c} ∈ cliqueComplex G := by
  rw [mem_cliqueComplex_iff]
  refine ⟨by simp, ?_⟩
  intro x hx y hy hxy
  simp only [Finset.coe_insert, Finset.coe_singleton,
    Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
  · exact (hxy rfl).elim
  · exact hab
  · exact hac
  · exact G.adj_symm hab
  · exact (hxy rfl).elim
  · exact hbc
  · exact G.adj_symm hac
  · exact G.adj_symm hbc
  · exact (hxy rfl).elim
end QEC.Coding.HighDimensionalExpander.CayleyClique
