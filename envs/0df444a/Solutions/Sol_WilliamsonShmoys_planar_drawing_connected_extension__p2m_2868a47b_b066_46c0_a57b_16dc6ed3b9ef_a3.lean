-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_extension__p2m_2868a47b_b066_46c0_a57b_16dc6ed3b9ef_a3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:20:03.750214+00:00
-- url     : https://prove2.me/submissions/f5e5a6db-edc3-42de-82d4-b45af3308ca9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_a4257fd8_446b_43ed_ae2f_f84ba74a352a_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_connected__p2m_a4257fd8_446b_43ed_ae2f_f84ba74a352a_a1
open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : HasPlanarDrawingOn G) (hcard : 3 ≤ Fintype.card V)
    (hconn : ¬ G.Connected) :
    ∃ H : SimpleGraph V, G ≤ H ∧ H.Connected ∧ HasPlanarDrawingOn H := by
  obtain ⟨H, hGH, hH, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension__p2m_a4257fd8_446b_43ed_ae2f_f84ba74a352a_a1
      G hG
  exact ⟨H, hGH, WilliamsonShmoys.maximal_planar_supergraph_connected__p2m_a4257fd8_446b_43ed_ae2f_f84ba74a352a_a1
    H hH hcard hmax, hH⟩