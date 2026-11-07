-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CayleyClique.card_cayley_extensionVertices_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:05:54.696548+00:00
-- url     : https://prove2.me/submissions/919ebd1f-71c4-4b08-a56b-7a37ca2c1141

import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
import Mathlib.Combinatorics.SimpleGraph.Cayley
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_CayleyClique
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CayleyClique_card_extensionVertices_le_neighbors
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CayleyClique_card_neighborVertices_cayley_le

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CayleyClique
open Finset
universe u v
variable {V : Type u} {W : Type v}
variable {Γ : Type u} [Group Γ]
variable [Fintype Γ] [DecidableEq Γ]
namespace QEC.Coding.HighDimensionalExpander.CayleyClique
theorem _root_.solution
    (S : Finset Γ) (s : Finset Γ) {x : Γ} (hx : x ∈ s) :
    (extensionVertices (cayleyCliqueComplex (S : Set Γ)) s).card ≤ 2 * S.card :=
  (card_extensionVertices_le_neighbors
    (SimpleGraph.mulCayley (S : Set Γ)) s hx).trans
      (card_neighborVertices_cayley_le S x)
end QEC.Coding.HighDimensionalExpander.CayleyClique
