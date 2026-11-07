-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CayleyClique.card_neighborVertices_schreier_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:53:07.465387+00:00
-- url     : https://prove2.me/submissions/7ddc428f-817b-4049-bff7-16f5867c590e

import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
import Mathlib.Combinatorics.SimpleGraph.Cayley
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_CayleyClique
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CayleyClique_neighborVertices_schreier_subset_candidates
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CayleyClique_card_schreierNeighborCandidates_le

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
    (neighborVertices (schreierGraph (X := X) (S : Set Γ)) x).card ≤ 2 * S.card :=
  (Finset.card_le_card (neighborVertices_schreier_subset_candidates S x)).trans
    (card_schreierNeighborCandidates_le S x)
end QEC.Coding.HighDimensionalExpander.CayleyClique
