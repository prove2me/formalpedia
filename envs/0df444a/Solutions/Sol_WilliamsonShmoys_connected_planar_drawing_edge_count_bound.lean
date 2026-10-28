-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_drawing_edge_count_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T14:33:26.189408+00:00
-- url     : https://prove2.me/submissions/5b7020e3-891b-4389-a7aa-7ad95b5a71f1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension_8575ae1d_620b_40d7_9b25_8ae2db919063
import Theorems.Thm_WilliamsonShmoys_edge_count_mono_8575ae1d_620b_40d7_9b25_8ae2db919063

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hQdraw : WilliamsonShmoys.HasPlanarDrawingOn Q)
    (hQconn : Q.Connected)
    (hCard : 3 ≤ Fintype.card V) :
    Q.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨R, hQR, _hRdraw, _hRconn, hRcard⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_extension_8575ae1d_620b_40d7_9b25_8ae2db919063
      Q hQdraw hQconn hCard
  have hmono : Q.edgeSet.ncard ≤ R.edgeSet.ncard :=
    WilliamsonShmoys.edge_count_mono_8575ae1d_620b_40d7_9b25_8ae2db919063 Q R hQR
  omega