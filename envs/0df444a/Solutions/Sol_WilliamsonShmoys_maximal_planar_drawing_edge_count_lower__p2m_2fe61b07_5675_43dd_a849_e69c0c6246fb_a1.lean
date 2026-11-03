-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_lower__p2m_2fe61b07_5675_43dd_a849_e69c0c6246fb_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:11:02.995207+00:00
-- url     : https://prove2.me/submissions/3795f2a9-8fca-4031-8c22-9fd1871807f2

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_triangulated_completion__p2m_5bb6036a_c064_4854_9d2e_96dfd53e9e35_a2
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hN : HasPlanarDrawingOn N)
    (hMax : forall K : SimpleGraph V, N <= K -> HasPlanarDrawingOn K -> K = N) :
    letI : DecidableRel N.Adj := Classical.decRel N.Adj
    3 * Fintype.card V - 6 <= N.edgeFinset.card := by
  classical
  obtain ⟨K, hNK, hK, hCount⟩ :=
    WilliamsonShmoys.planar_drawing_has_triangulated_completion__p2m_5bb6036a_c064_4854_9d2e_96dfd53e9e35_a2
      N hV hN
  have hEq : K = N := hMax K hNK hK
  subst K
  omega