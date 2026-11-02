-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_extends_to_triangulation__p2m_e13857bb_dfd7_4e7a_a1e7_eab5feffe183_a3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:52:28.287245+00:00
-- url     : https://prove2.me/submissions/4716ba1c-64b7-43cc-8287-f2f5c8970177
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_extends_to_edge_maximal__p2m_a40304d1_03ef_470a_a877_21a5de02f724_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_a40304d1_03ef_470a_a877_21a5de02f724_a1

open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) [DecidableRel L.Adj]
    (hL : HasPlanarDrawingOn L)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V, ∃ (dH : DecidableRel H.Adj),
      (letI : DecidableRel H.Adj := dH
       L.edgeFinset ⊆ H.edgeFinset ∧ HasPlanarDrawingOn H ∧
       H.edgeFinset.card + 6 = 3 * Fintype.card V) := by
  obtain ⟨H, dH, hdata⟩ :=
    WilliamsonShmoys.planar_drawing_extends_to_edge_maximal__p2m_a40304d1_03ef_470a_a877_21a5de02f724_a1
      L hL hcard
  letI : DecidableRel H.Adj := dH
  obtain ⟨hsub, hH, hmax⟩ := hdata
  have hcount :=
    WilliamsonShmoys.maximal_planar_edge_count__p2m_a40304d1_03ef_470a_a877_21a5de02f724_a1
      H hH hcard hmax
  exact ⟨H, dH, hsub, hH, hcount⟩