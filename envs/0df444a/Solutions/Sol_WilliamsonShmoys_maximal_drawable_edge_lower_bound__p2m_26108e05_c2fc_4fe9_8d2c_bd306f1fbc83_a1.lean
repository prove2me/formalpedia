-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_edge_lower_bound__p2m_26108e05_c2fc_4fe9_8d2c_bd306f1fbc83_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T19:51:13.976502+00:00
-- url     : https://prove2.me/submissions/c04684cd-bd1f-4ee3-8e22-a2bc49c23a5f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_locally_maximal_planar_edge_bound__p2m_36354cce_e9f2_4cf3_abf4_0b18020ca45b_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L.edgeSet.ncard ≤ K.edgeSet.ncard) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  apply WilliamsonShmoys.locally_maximal_planar_edge_bound__p2m_36354cce_e9f2_4cf3_abf4_0b18020ca45b_a1
    K hCard hDraw
  intro L hSub hOneMore hPlanar
  have hBound := hMax L hSub hPlanar
  omega