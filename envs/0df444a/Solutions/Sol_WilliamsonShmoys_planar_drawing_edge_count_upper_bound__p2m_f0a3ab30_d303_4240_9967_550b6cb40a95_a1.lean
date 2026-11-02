-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_count_upper_bound__p2m_f0a3ab30_d303_4240_9967_550b6cb40a95_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:33:37.3128+00:00
-- url     : https://prove2.me/submissions/d5276b73-9287-40c9-9304-4a38c6f9faf2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_completion__p2m_0951cfca_b350_4b14_85c9_9d9dc14f4b38_a3
import Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_edge_count__p2m_0951cfca_b350_4b14_85c9_9d9dc14f4b38_a3
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V) (hJ : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hcard : 3 <= Fintype.card V) :
    letI : ∀ K : SimpleGraph V, DecidableRel K.Adj :=
      fun K => Classical.decRel K.Adj
    J.edgeFinset.card <= 3 * Fintype.card V - 6 := by
  classical
  letI : ∀ K : SimpleGraph V, DecidableRel K.Adj :=
    fun K => Classical.decRel K.Adj
  obtain ⟨H, hHdraw, hHconn, hsub⟩ :=
    WilliamsonShmoys.planar_drawing_connected_completion__p2m_0951cfca_b350_4b14_85c9_9d9dc14f4b38_a3 J hJ
  have hbound :=
    WilliamsonShmoys.connected_planar_drawing_edge_count__p2m_0951cfca_b350_4b14_85c9_9d9dc14f4b38_a3 H hHdraw hHconn hcard
  exact le_trans (Finset.card_le_card hsub) hbound