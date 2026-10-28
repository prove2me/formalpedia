-- Prove2me | solution 1 for WilliamsonShmoys.exists_triangulated_planar_supergraph_on
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T19:58:47.183352+00:00
-- url     : https://prove2.me/submissions/2f7520b3-1e49-409a-a363-c84d9e70647f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_on
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_on

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hKplanar : HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧ HasPlanarDrawingOn H ∧
        H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨H, hKH, hHmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph_on K hKplanar
  refine ⟨H, hKH, hHmax.1, ?_⟩
  exact WilliamsonShmoys.maximal_planar_edge_count_on H hHmax hV