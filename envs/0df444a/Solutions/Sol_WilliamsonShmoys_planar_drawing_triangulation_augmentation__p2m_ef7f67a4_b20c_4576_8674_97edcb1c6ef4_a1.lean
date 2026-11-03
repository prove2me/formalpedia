-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_augmentation__p2m_ef7f67a4_b20c_4576_8674_97edcb1c6ef4_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T16:12:13.494683+00:00
-- url     : https://prove2.me/submissions/f00cb47f-fec8-4fd3-b414-f9479f19940c

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_d2e6787a_41a9_4272_bec1_4c170f4b8b09_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hM : HasPlanarDrawingOn M) :
    (letI : (G : SimpleGraph V) → DecidableRel G.Adj :=
      fun G => Classical.decRel G.Adj
     ∃ H : SimpleGraph V, M ≤ H ∧ HasPlanarDrawingOn H ∧
       H.edgeFinset.card = 3 * Fintype.card V - 6) := by
  obtain ⟨H, hsub, hdraw, hcount⟩ :=
    WilliamsonShmoys.planar_triangulation_extension__p2m_d2e6787a_41a9_4272_bec1_4c170f4b8b09_a1 M hM hcard
  refine ⟨H, hsub, hdraw, ?_⟩
  omega