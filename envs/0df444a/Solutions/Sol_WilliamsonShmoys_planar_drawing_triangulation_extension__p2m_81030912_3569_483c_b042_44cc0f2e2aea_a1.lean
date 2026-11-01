-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_81030912_3569_483c_b042_44cc0f2e2aea_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:09:02.322143+00:00
-- url     : https://prove2.me/submissions/549312b5-21df-44c7-b044-1b248e700c59
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_2fffb22b_bc54_424c_9398_721fe1492b46_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_2fffb22b_bc54_424c_9398_721fe1492b46_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hK : HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ (H : SimpleGraph V) (dH : DecidableRel H.Adj),
      (letI : DecidableRel K.Adj := dK
       letI : DecidableRel H.Adj := dH
       K.edgeFinset ⊆ H.edgeFinset) ∧
      (letI : DecidableRel H.Adj := dH
       H.edgeFinset.card = 3 * Fintype.card V - 6) := by
  obtain ⟨H, dH, hKH, hH, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension__p2m_2fffb22b_bc54_424c_9398_721fe1492b46_a1
      K dK hK hcard
  refine ⟨H, dH, ?_, ?_⟩
  · letI : DecidableRel K.Adj := dK
    letI : DecidableRel H.Adj := dH
    exact hKH
  · exact WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_2fffb22b_bc54_424c_9398_721fe1492b46_a1
      H dH hH hmax hcard