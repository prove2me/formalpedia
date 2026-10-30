-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_ce9f6242_56a0_4c10_94b5_7a9007787131_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:44:44.181524+00:00
-- url     : https://prove2.me/submissions/f376085d-305c-4756-96d3-49d2562aff5e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_e52f58d6_33ee_4b8e_a7a8_0fe00cf44d7c_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_e52f58d6_33ee_4b8e_a7a8_0fe00cf44d7c_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ (H : SimpleGraph V) (dH : DecidableRel H.Adj),
      (letI : DecidableRel H.Adj := dH
       K ≤ H ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
       H.edgeFinset.card = 3 * Fintype.card V - 6 ∧
       K.edgeFinset.card ≤ H.edgeFinset.card) := by
  classical
  obtain ⟨H, dH, h⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension__p2m_e52f58d6_33ee_4b8e_a7a8_0fe00cf44d7c_a1
      K hK hconn hcard
  letI : DecidableRel H.Adj := dH
  rcases h with ⟨hKH, hHconn, hHdraw, hmax, hcount_le⟩
  have hcount :=
    WilliamsonShmoys.maximal_planar_edge_count__p2m_e52f58d6_33ee_4b8e_a7a8_0fe00cf44d7c_a1
      H dH hHdraw hHconn hmax hcard
  refine ⟨H, dH, ?_⟩
  letI : DecidableRel H.Adj := dH
  exact ⟨hKH, hHconn, hHdraw, hcount, hcount_le⟩