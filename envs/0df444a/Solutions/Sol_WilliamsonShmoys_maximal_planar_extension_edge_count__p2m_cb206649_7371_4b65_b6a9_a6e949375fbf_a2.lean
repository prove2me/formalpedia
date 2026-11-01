-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_extension_edge_count__p2m_cb206649_7371_4b65_b6a9_a6e949375fbf_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:09:22.919795+00:00
-- url     : https://prove2.me/submissions/0449852a-8f6c-4f0f-81f1-ad669b73e709
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_extension_exists__p2m_89582c96_c588_4663_9e82_ebaf767d7a60_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_extension_edge_count__p2m_89582c96_c588_4663_9e82_ebaf767d7a60_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel K.Adj := Classical.decRel K.Adj;
      ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧
        (letI : DecidableRel L.Adj := Classical.decRel L.Adj;
          3 * Fintype.card V - 6 = L.edgeFinset.card)) := by
  classical
  letI : DecidableRel K.Adj := Classical.decRel K.Adj
  obtain ⟨L, hKL, hL, hmax⟩ :=
    WilliamsonShmoys.maximal_planar_drawing_extension_exists__p2m_89582c96_c588_4663_9e82_ebaf767d7a60_a1
      K hK hcard
  refine ⟨L, hKL, hL, ?_⟩
  exact WilliamsonShmoys.maximal_planar_extension_edge_count__p2m_89582c96_c588_4663_9e82_ebaf767d7a60_a1
    L hL hcard hmax