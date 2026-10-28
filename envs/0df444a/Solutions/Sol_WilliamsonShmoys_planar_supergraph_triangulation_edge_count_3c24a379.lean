-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_triangulation_edge_count_3c24a379
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T06:36:20.3247+00:00
-- url     : https://prove2.me/submissions/ba2ebfe8-9435-4238-a4b1-668d4caad111
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_exists_maximal_f1f92bb7
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_f1f92bb7

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V, K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
      3 * Fintype.card V = L.edgeSet.ncard + 6 := by
  obtain ⟨L, hKL, hL, hMax⟩ :=
    WilliamsonShmoys.planar_supergraph_exists_maximal_f1f92bb7 K hK
  exact ⟨L, hKL, hL,
    WilliamsonShmoys.maximal_planar_edge_count_f1f92bb7 L hL hCard hMax⟩