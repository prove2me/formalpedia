-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_533c1536_70f9_4baf_8d8d_aa7e4273cff9_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:16:35.181169+00:00
-- url     : https://prove2.me/submissions/a198bee2-cb09-43c4-a84c-4150afff97c3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_simple_edge_bound__p2m_a7b1543f_eb9f_42ef_b47d_96ddc7610efd_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_a7b1543f_eb9f_42ef_b47d_96ddc7610efd_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hH : HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K ≤ H) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hupper := WilliamsonShmoys.planar_simple_edge_bound__p2m_a7b1543f_eb9f_42ef_b47d_96ddc7610efd_a1 H hcard hH
  have hlower := WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_a7b1543f_eb9f_42ef_b47d_96ddc7610efd_a1 H hcard hH hmax
  omega