-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CayleyClique.extensionVertices_subset_neighborVertices
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:51:18.574065+00:00
-- url     : https://prove2.me/submissions/fa9a859a-809b-475b-835b-e2ba427ea89d

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
    (G : SimpleGraph V) (s : Finset V) {x : V} (hx : x ∈ s) :
    extensionVertices (cliqueComplex G) s ⊆ neighborVertices G x := by
  intro y hy
  rw [mem_extensionVertices_iff] at hy
  rw [mem_neighborVertices_iff]
  exact hy.2.2 (by exact Finset.mem_insert_of_mem hx) (by simp) (by
    intro hxy
    subst y
    exact hy.1 hx)
end QEC.Coding.HighDimensionalExpander.CayleyClique
