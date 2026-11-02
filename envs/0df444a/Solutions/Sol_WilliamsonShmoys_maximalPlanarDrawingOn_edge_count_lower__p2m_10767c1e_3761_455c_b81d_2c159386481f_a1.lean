-- Prove2me | solution 1 for WilliamsonShmoys.maximalPlanarDrawingOn_edge_count_lower__p2m_10767c1e_3761_455c_b81d_2c159386481f_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:56:54.680225+00:00
-- url     : https://prove2.me/submissions/975b1017-2863-4c3b-888c-048271842bc8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximalPlanarDrawingOn_euler_face_counts__p2m_77e6a9aa_019b_4811_bd18_07d7e3258778_a1
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K) :
    3 * Fintype.card V - 6 ≤ K.edgeSet.ncard := by
  obtain ⟨f, hFaces, hEuler⟩ :=
    WilliamsonShmoys.maximalPlanarDrawingOn_euler_face_counts__p2m_77e6a9aa_019b_4811_bd18_07d7e3258778_a1
      K hK hCard hmax
  omega