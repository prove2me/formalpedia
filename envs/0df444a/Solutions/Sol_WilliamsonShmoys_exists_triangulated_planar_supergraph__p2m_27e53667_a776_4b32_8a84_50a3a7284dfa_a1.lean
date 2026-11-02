-- Prove2me | solution 1 for WilliamsonShmoys.exists_triangulated_planar_supergraph__p2m_27e53667_a776_4b32_8a84_50a3a7284dfa_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:56:39.56411+00:00
-- url     : https://prove2.me/submissions/c442ba36-6b06-42be-a192-92bbb9b529a7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_56b77430_5edc_41bf_8724_d4c1ab81c0d8_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_56b77430_5edc_41bf_8724_d4c1ab81c0d8_a1

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hcard : LE.le 3 (Fintype.card V))
    (hMdraw : HasPlanarDrawingOn M) :
    Exists fun N : SimpleGraph V => And (LE.le M N) (And (HasPlanarDrawingOn N)
      (3 * Fintype.card V =
        (letI : DecidableRel N.Adj := Classical.decRel N.Adj
         N.edgeFinset.card) + 6)) := by
  obtain ⟨N, hMN, hNdraw, hNmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_56b77430_5edc_41bf_8724_d4c1ab81c0d8_a1
      M hcard hMdraw
  have hcount :=
    WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_56b77430_5edc_41bf_8724_d4c1ab81c0d8_a1
      N hcard hNdraw hNmax
  exact ⟨N, hMN, hNdraw, hcount⟩