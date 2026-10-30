-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_extension__p2m_caacfef8_9dba_490e_9e07_b3138fa16d65_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:40:43.85317+00:00
-- url     : https://prove2.me/submissions/0f2dcf2d-f610-4239-ae9f-d963b156ee31
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_ffd3f69d_18cc_4be0_84fa_2bff696b22a9_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_ffd3f69d_18cc_4be0_84fa_2bff696b22a9_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V, M ≤ H ∧ HasPlanarDrawingOn H ∧
      (letI : DecidableRel H.Adj := Classical.decRel H.Adj;
        H.edgeFinset.card = 3 * Fintype.card V - 6) := by
  obtain ⟨H, hMH, hH, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension__p2m_ffd3f69d_18cc_4be0_84fa_2bff696b22a9_a2
      M hM
  refine ⟨H, hMH, hH, ?_⟩
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  exact WilliamsonShmoys.maximal_planar_edge_count__p2m_ffd3f69d_18cc_4be0_84fa_2bff696b22a9_a2
    H hH hmax hcard