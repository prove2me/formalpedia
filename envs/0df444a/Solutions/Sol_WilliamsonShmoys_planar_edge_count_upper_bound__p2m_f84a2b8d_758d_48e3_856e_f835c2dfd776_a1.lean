-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound__p2m_f84a2b8d_758d_48e3_856e_f835c2dfd776_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:41:17.700547+00:00
-- url     : https://prove2.me/submissions/b489d040-d81e-4f17-b37d-4fd5ee798594
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawable_maximal_extension__p2m_bef9e736_66c4_4a44_9d5c_f3c0ae5dba68_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_bef9e736_66c4_4a44_9d5c_f3c0ae5dba68_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hN : HasPlanarDrawingOn N) :
    (letI : DecidableRel N.Adj := Classical.decRel N.Adj;
      N.edgeFinset.card + 6 ≤ 3 * Fintype.card V) := by
  classical
  obtain ⟨H, hNH, hPlanarH, hMono, hMax⟩ :=
    WilliamsonShmoys.planar_drawable_maximal_extension__p2m_bef9e736_66c4_4a44_9d5c_f3c0ae5dba68_a1 N hN
  have hExact :=
    WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_bef9e736_66c4_4a44_9d5c_f3c0ae5dba68_a1 H hPlanarH hV hMax
  omega