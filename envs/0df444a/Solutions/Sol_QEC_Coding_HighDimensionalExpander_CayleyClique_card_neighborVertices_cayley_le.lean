-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CayleyClique.card_neighborVertices_cayley_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:52:20.244702+00:00
-- url     : https://prove2.me/submissions/e3424fdb-a8f9-4531-afe4-5469f6c4e841

import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
import Mathlib.Combinatorics.SimpleGraph.Cayley
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_CayleyClique
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CayleyClique_neighborVertices_cayley_subset_candidates
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CayleyClique_card_cayleyNeighborCandidates_le

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CayleyClique
open Finset
universe u v
variable {V : Type u} {W : Type v}
variable {Γ : Type u} [Group Γ]
variable [Fintype Γ] [DecidableEq Γ]
namespace QEC.Coding.HighDimensionalExpander.CayleyClique
theorem _root_.solution (S : Finset Γ) (x : Γ) :
    (neighborVertices (SimpleGraph.mulCayley (S : Set Γ)) x).card ≤ 2 * S.card :=
  (Finset.card_le_card (neighborVertices_cayley_subset_candidates S x)).trans
    (card_cayleyNeighborCandidates_le S x)
end QEC.Coding.HighDimensionalExpander.CayleyClique
