-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_upper_bound__p2m_c0d4ecaf_266f_445a_8f51_dc327adf9453_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:45:57.989365+00:00
-- url     : https://prove2.me/submissions/c34d6811-ecaa-4d0f-87aa-4f35621f84d7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_supergraph_edge_count__p2m_c52ee0f6_cd77_40cf_a2f0_4d029ef0159f_a2

set_option autoImplicit false

open scoped BigOperators

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    K.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨H, hKH, hH, hHcard⟩ :=
    WilliamsonShmoys.planar_triangulation_supergraph_edge_count__p2m_c52ee0f6_cd77_40cf_a2f0_4d029ef0159f_a2
      K hcard hK
  exact (Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hKH)).trans_eq hHcard