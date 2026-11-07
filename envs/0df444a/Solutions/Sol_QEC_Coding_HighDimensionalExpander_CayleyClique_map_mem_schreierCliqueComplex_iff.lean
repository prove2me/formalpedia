-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CayleyClique.map_mem_schreierCliqueComplex_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:51:55.571482+00:00
-- url     : https://prove2.me/submissions/3f5860fd-00dd-4bae-9bc5-28a4a2a3fb88

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
namespace QEC.Coding.HighDimensionalExpander.CayleyClique
theorem _root_.solution
    (S : Set Γ) (e : X ≃ X) (h : ∀ g ∈ S, ∀ x, e (g • x) = g • e x)
    (s : Finset X) :
    s.map e.toEmbedding ∈ schreierCliqueComplex S ↔ s ∈ schreierCliqueComplex S :=
  map_mem_cliqueComplex_iff (schreierIsoOfCommutes S e h) s
end QEC.Coding.HighDimensionalExpander.CayleyClique
