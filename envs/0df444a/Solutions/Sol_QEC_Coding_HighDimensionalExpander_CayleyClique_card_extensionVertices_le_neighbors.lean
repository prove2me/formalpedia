-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CayleyClique.card_extensionVertices_le_neighbors
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:51:51.203949+00:00
-- url     : https://prove2.me/submissions/ae586fc1-9e23-45e5-8028-37578c80961d

import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
import Mathlib.Combinatorics.SimpleGraph.Cayley
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_CayleyClique
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CayleyClique_extensionVertices_subset_neighborVertices

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CayleyClique
open Finset
universe u v
variable {V : Type u} {W : Type v}
variable [Fintype V] [DecidableEq V]
namespace QEC.Coding.HighDimensionalExpander.CayleyClique
theorem _root_.solution
    (G : SimpleGraph V) (s : Finset V) {x : V} (hx : x ∈ s) :
    (extensionVertices (cliqueComplex G) s).card ≤ (neighborVertices G x).card := by
  exact Finset.card_le_card (extensionVertices_subset_neighborVertices G s hx)
end QEC.Coding.HighDimensionalExpander.CayleyClique
