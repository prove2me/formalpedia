-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_augmentation__p2m_2ea99569_5736_493f_8895_a821efa27469_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:01:39.635093+00:00
-- url     : https://prove2.me/submissions/d11be26f-200b-4cec-ba8b-30402ee4fad4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_db2bc25d_3c02_46be_91b6_cd4d6f11e2cd_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_db2bc25d_3c02_46be_91b6_cd4d6f11e2cd_a1

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hG : HasPlanarDrawingOn G) :
    ∃ R : SimpleGraph V, G <= R ∧ HasPlanarDrawingOn R ∧
      (letI : DecidableRel R.Adj := Classical.decRel R.Adj
       3 * Fintype.card V = R.edgeFinset.card + 6) := by
  obtain ⟨R, hGR, hR, hMax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension__p2m_db2bc25d_3c02_46be_91b6_cd4d6f11e2cd_a1
      G hG
  refine ⟨R, hGR, hR, ?_⟩
  letI : DecidableRel R.Adj := Classical.decRel R.Adj
  exact WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_db2bc25d_3c02_46be_91b6_cd4d6f11e2cd_a1
    R hV hR hMax
