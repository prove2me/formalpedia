-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CayleyClique.card_schreierNeighborCandidates_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:51:56.591073+00:00
-- url     : https://prove2.me/submissions/8490999f-f2f3-42ac-82a1-1f19c7411a79

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
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
variable [Fintype X] [DecidableEq X] [DecidableEq Γ]
omit [Fintype X] [DecidableEq Γ]
namespace QEC.Coding.HighDimensionalExpander.CayleyClique
theorem _root_.solution (S : Finset Γ) (x : X) :
    (schreierNeighborCandidates S x).card ≤ 2 * S.card := by
  calc
    (schreierNeighborCandidates S x).card ≤
        (S.image fun g => g • x).card + (S.image fun g => g⁻¹ • x).card :=
      Finset.card_union_le _ _
    _ ≤ S.card + S.card := Nat.add_le_add Finset.card_image_le Finset.card_image_le
    _ = 2 * S.card := by omega
end QEC.Coding.HighDimensionalExpander.CayleyClique
