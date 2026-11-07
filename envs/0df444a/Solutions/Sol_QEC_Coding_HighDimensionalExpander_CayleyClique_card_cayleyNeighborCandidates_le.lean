-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CayleyClique.card_cayleyNeighborCandidates_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:51:35.802176+00:00
-- url     : https://prove2.me/submissions/8d96e2c8-96ef-4f0e-b281-ea1cc981c5ee

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
omit [Fintype Γ]
namespace QEC.Coding.HighDimensionalExpander.CayleyClique
theorem _root_.solution (S : Finset Γ) (x : Γ) :
    (cayleyNeighborCandidates S x).card ≤ 2 * S.card := by
  calc
    (cayleyNeighborCandidates S x).card ≤
        (S.image fun g => x * g).card + (S.image fun g => x * g⁻¹).card :=
      Finset.card_union_le _ _
    _ ≤ S.card + S.card := Nat.add_le_add Finset.card_image_le Finset.card_image_le
    _ = 2 * S.card := by omega
end QEC.Coding.HighDimensionalExpander.CayleyClique
