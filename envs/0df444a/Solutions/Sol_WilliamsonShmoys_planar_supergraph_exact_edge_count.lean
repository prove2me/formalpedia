-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_exact_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T01:22:30.734982+00:00
-- url     : https://prove2.me/submissions/6921e958-9aef-425b-847b-37a85e159fe9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_same_vertex_edge_maximal_planar_extension_d91007ea_2b83_4647_90f6_3b32f55c223e
import Theorems.Thm_WilliamsonShmoys_edge_count_of_same_vertex_edge_maximal_planar_d91007ea_2b83_4647_90f6_3b32f55c223e

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      (∀ ⦃u v⦄, L.Adj u v → K.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hLK, hK, hmax⟩ :=
    WilliamsonShmoys.exists_same_vertex_edge_maximal_planar_extension_d91007ea_2b83_4647_90f6_3b32f55c223e L hL
  exact ⟨K, hLK, hK,
    WilliamsonShmoys.edge_count_of_same_vertex_edge_maximal_planar_d91007ea_2b83_4647_90f6_3b32f55c223e K hK hV hmax⟩