-- Prove2me | solution 2 for WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_d5fb2175_2340_4982_8e4d_d8f2c0e58052_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:33:12.17934+00:00
-- url     : https://prove2.me/submissions/ebe426be-3f6a-4434-bdc3-1d92da77c9a9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_completion__p2m_ec87327c_94d1_4f33_a35a_c8476e7ad1f3_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hDraw : HasPlanarDrawingOn H)
    (hMax : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H)
    (hCard : 3 ≤ Fintype.card V) : H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hHK, hKDraw, hCount⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_completion__p2m_ec87327c_94d1_4f33_a35a_c8476e7ad1f3_a1
      H hDraw hCard
  have hEq : K = H := hMax K hHK hKDraw
  rw [hEq] at hCount
  exact hCount