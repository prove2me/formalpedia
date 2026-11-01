-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_edge_bound__p2m_1d9982e7_ae2e_41b5_99c8_f768b7d6d77d_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:32:46.635491+00:00
-- url     : https://prove2.me/submissions/5c7e8283-fb45-4c23-8dd6-224da368ec32
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension__p2m_52ae77ae_f85b_40f5_bd03_34373df951b6_a3
import Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_edge_bound__p2m_52ae77ae_f85b_40f5_bd03_34373df951b6_a2
import Theorems.Thm_WilliamsonShmoys_edge_bound_of_subgraph_bound__p2m_52ae77ae_f85b_40f5_bd03_34373df951b6_a2

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : HasPlanarDrawingOn K)
    (hcard : 3 <= Fintype.card V) :
    K.edgeFinset.card + 6 <= 3 * Fintype.card V := by
  classical
  obtain ⟨H, hKH, hHconnected, hHdrawing⟩ :=
    WilliamsonShmoys.planar_drawing_connected_extension__p2m_52ae77ae_f85b_40f5_bd03_34373df951b6_a3
      K hK hcard
  have hHbound :=
    WilliamsonShmoys.connected_planar_drawing_edge_bound__p2m_52ae77ae_f85b_40f5_bd03_34373df951b6_a2
      H hHdrawing hHconnected hcard
  exact WilliamsonShmoys.edge_bound_of_subgraph_bound__p2m_52ae77ae_f85b_40f5_bd03_34373df951b6_a2
    K H hKH hHbound