-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CayleyClique.neighborVertices_schreier_subset_candidates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:52:27.08867+00:00
-- url     : https://prove2.me/submissions/4bdf7c25-21a7-4f8d-8ea8-9baab4379c2d

import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
import Mathlib.Combinatorics.SimpleGraph.Cayley
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_CayleyClique
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CayleyClique_map_mem_schreierCliqueComplex_iff
attribute [local simp] QEC.Coding.HighDimensionalExpander.CayleyClique.map_mem_schreierCliqueComplex_iff

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CayleyClique
open Finset
universe u v
variable {V : Type u} {W : Type v}
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
variable [Fintype X] [DecidableEq X] [DecidableEq Γ]
omit [DecidableEq Γ]
namespace QEC.Coding.HighDimensionalExpander.CayleyClique
theorem _root_.solution (S : Finset Γ) (x : X) :
    neighborVertices (schreierGraph (X := X) (S : Set Γ)) x ⊆
      schreierNeighborCandidates S x := by
  intro y hy
  rw [mem_neighborVertices_iff, schreierGraph_adj] at hy
  rcases hy with ⟨_, g, hg, hgy⟩ | ⟨_, g, hg, hgy⟩
  · apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨g, hg, hgy⟩
  · apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    refine ⟨g, hg, ?_⟩
    calc
      g⁻¹ • x = g⁻¹ • (g • y) := by rw [hgy]
      _ = y := by simp
end QEC.Coding.HighDimensionalExpander.CayleyClique
