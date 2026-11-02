-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_56b77430_5edc_41bf_8724_d4c1ab81c0d8_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:55:22.971217+00:00
-- url     : https://prove2.me/submissions/7b58c754-fd0a-43a5-8641-e2f7473aab44
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_f8e496dc_ac86_4dbf_b6d9_446222a8ec24_a2

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hcard : LE.le 3 (Fintype.card V))
    (hNdraw : HasPlanarDrawingOn N)
    (hmax : forall K : SimpleGraph V, LE.le N K -> HasPlanarDrawingOn K -> K = N) :
    3 * Fintype.card V =
      (letI : DecidableRel N.Adj := Classical.decRel N.Adj
       N.edgeFinset.card) + 6 := by
  have hExt :=
    WilliamsonShmoys.planar_triangulation_extension__p2m_f8e496dc_ac86_4dbf_b6d9_446222a8ec24_a2
      N hcard hNdraw
  apply Exists.elim hExt
  intro K hK
  have hNK : LE.le N K := hK.1
  have hKdraw : HasPlanarDrawingOn K := hK.2.1
  have hKcard :=
    hK.2.2
  have hKN : K = N := hmax K hNK hKdraw
  rw [hKN] at hKcard
  exact hKcard