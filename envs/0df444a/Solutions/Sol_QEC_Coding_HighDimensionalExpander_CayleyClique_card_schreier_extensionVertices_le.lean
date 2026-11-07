-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CayleyClique.card_schreier_extensionVertices_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:05:55.913266+00:00
-- url     : https://prove2.me/submissions/86345107-82aa-4a50-b7c4-cce4a27474e6

import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
import Mathlib.Combinatorics.SimpleGraph.Cayley
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_CayleyClique
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CayleyClique_card_extensionVertices_le_neighbors
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CayleyClique_card_neighborVertices_schreier_le

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CayleyClique
open Finset
universe u v
variable {V : Type u} {W : Type v}
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
variable [Fintype X] [DecidableEq X] [DecidableEq Γ]
omit [DecidableEq Γ]
namespace QEC.Coding.HighDimensionalExpander.CayleyClique
theorem _root_.solution
    (S : Finset Γ) (s : Finset X) {x : X} (hx : x ∈ s) :
    (extensionVertices (schreierCliqueComplex (X := X) (S : Set Γ)) s).card ≤
      2 * S.card :=
  (card_extensionVertices_le_neighbors
    (schreierGraph (X := X) (S : Set Γ)) s hx).trans
      (card_neighborVertices_schreier_le S x)
end QEC.Coding.HighDimensionalExpander.CayleyClique
