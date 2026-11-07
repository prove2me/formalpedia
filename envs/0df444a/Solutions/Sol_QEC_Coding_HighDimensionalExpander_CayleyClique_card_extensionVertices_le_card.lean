-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CayleyClique.card_extensionVertices_le_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:05:51.857657+00:00
-- url     : https://prove2.me/submissions/71a8a24e-15b8-49cd-a17c-f4105f80d38b

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
variable [Fintype V] [DecidableEq V]
namespace QEC.Coding.HighDimensionalExpander.CayleyClique
theorem _root_.solution
    (K : AbstractSimplicialComplex V) (s : Finset V) :
    (extensionVertices K s).card ≤ Fintype.card V := by
  classical
  simpa using Finset.card_le_card (Finset.subset_univ (extensionVertices K s))
end QEC.Coding.HighDimensionalExpander.CayleyClique
