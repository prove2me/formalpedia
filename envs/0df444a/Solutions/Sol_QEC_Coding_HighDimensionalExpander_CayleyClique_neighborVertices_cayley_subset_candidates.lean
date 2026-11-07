-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CayleyClique.neighborVertices_cayley_subset_candidates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:51:33.375905+00:00
-- url     : https://prove2.me/submissions/12407ebf-7590-44e3-a68f-510299105d7a

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
variable {Γ : Type u} [Group Γ]
variable [Fintype Γ] [DecidableEq Γ]
namespace QEC.Coding.HighDimensionalExpander.CayleyClique
theorem _root_.solution (S : Finset Γ) (x : Γ) :
    neighborVertices (SimpleGraph.mulCayley (S : Set Γ)) x ⊆
      cayleyNeighborCandidates S x := by
  intro y hy
  rw [mem_neighborVertices_iff, SimpleGraph.mulCayley_adj] at hy
  rcases hy.2 with h | h
  · apply Finset.mem_union_left
    apply Finset.mem_image.mpr
    exact ⟨x⁻¹ * y, h, by simp⟩
  · apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    exact ⟨y⁻¹ * x, h, by simp⟩
end QEC.Coding.HighDimensionalExpander.CayleyClique
