-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_54b85171_3c84_49d0_b75e_a1ac45808ba4_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:48:50.719409+00:00
-- url     : https://prove2.me/submissions/efc68d55-2ac0-42d4-ba07-7885ed623483
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_upper_bound__p2m_8b804cdd_68ca_48da_bde7_dd4a5c81f51a_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_8b804cdd_68ca_48da_bde7_dd4a5c81f51a_a2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hplanar : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hmax : forall K : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn K -> N <= K -> K = N)
    (hcard : 3 <= Fintype.card V) :
    N.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hupper := WilliamsonShmoys.maximal_planar_edge_count_upper_bound__p2m_8b804cdd_68ca_48da_bde7_dd4a5c81f51a_a2
    N hplanar hcard
  have hlower := WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_8b804cdd_68ca_48da_bde7_dd4a5c81f51a_a2
    N hplanar hmax hcard
  omega