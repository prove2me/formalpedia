-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_triangulation_supergraph__p2m_24d4a109_2712_447f_b6c6_168aeb4ef393_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:56:45.525603+00:00
-- url     : https://prove2.me/submissions/0a16283d-fb59-4d68-a5b6-14360e8262a5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_exists_maximum_planar_supergraph__p2m_c11f1659_d0fc_4751_a84f_f498781343a5_a1
import Theorems.Thm_WilliamsonShmoys_maximum_planar_graph_edge_count__p2m_c11f1659_d0fc_4751_a84f_f498781343a5_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (dH : DecidableRel H.Adj)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      H.edgeFinset ⊆ K.edgeFinset ∧
      K.edgeFinset.card + 6 = 3 * Fintype.card V := by
  obtain ⟨K, dK, hK, hHK, hmax⟩ :=
    WilliamsonShmoys.exists_maximum_planar_supergraph__p2m_c11f1659_d0fc_4751_a84f_f498781343a5_a1 H dH hH
  exact ⟨K, dK, hK, hHK,
    WilliamsonShmoys.maximum_planar_graph_edge_count__p2m_c11f1659_d0fc_4751_a84f_f498781343a5_a1 K dK hcard hK hmax⟩
