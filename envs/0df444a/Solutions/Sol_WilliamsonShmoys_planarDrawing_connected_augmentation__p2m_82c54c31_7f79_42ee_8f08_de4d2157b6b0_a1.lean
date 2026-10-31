-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawing_connected_augmentation__p2m_82c54c31_7f79_42ee_8f08_de4d2157b6b0_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:18:50.881201+00:00
-- url     : https://prove2.me/submissions/eea9bb78-f895-41db-9883-a062371f025e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planarDrawing_connected_supergraph_geometric_step__p2m_e22a771a_7e28_4296_9438_b0a9d74716aa_a2

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      H.Connected ∧ HasPlanarDrawingOn H ∧ K.edgeSet.ncard ≤ H.edgeSet.ncard := by
  obtain ⟨H, hKH, hconn, hplanar, hcard⟩ :=
    WilliamsonShmoys.planarDrawing_connected_supergraph_geometric_step__p2m_e22a771a_7e28_4296_9438_b0a9d74716aa_a2
      K hK hV
  exact ⟨H, hconn, hplanar, hcard⟩