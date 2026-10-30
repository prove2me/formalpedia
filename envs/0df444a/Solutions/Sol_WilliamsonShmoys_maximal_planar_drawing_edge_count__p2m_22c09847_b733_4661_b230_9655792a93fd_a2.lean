-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_22c09847_b733_4661_b230_9655792a93fd_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:55:44.347963+00:00
-- url     : https://prove2.me/submissions/c262b04d-dba0-48c1-9ab7-215d320a2fd3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_completion_edge_count__p2m_4bba7018_1c53_4b13_9fef_465486d61827_a1
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hHK, hKplanar, hKcount⟩ :=
    WilliamsonShmoys.planar_drawing_completion_edge_count__p2m_4bba7018_1c53_4b13_9fef_465486d61827_a1
      H hH hV
  have hKH : K = H := hMax K hHK hKplanar
  rw [hKH] at hKcount
  exact hKcount