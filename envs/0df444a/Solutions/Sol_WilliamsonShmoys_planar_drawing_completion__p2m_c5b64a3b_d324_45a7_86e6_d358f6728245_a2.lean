-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_completion__p2m_c5b64a3b_d324_45a7_86e6_d358f6728245_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T20:54:49.400411+00:00
-- url     : https://prove2.me/submissions/927217b9-ca52-40ff-882b-dd55b3ce3e39
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_exists__p2m_89b917c7_2895_4f7d_ae75_caac4f55b041_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_has_euler_edge_count__p2m_89b917c7_2895_4f7d_ae75_caac4f55b041_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ (J : SimpleGraph V) (dJ : DecidableRel J.Adj),
      G ≤ J ∧ WilliamsonShmoys.HasPlanarDrawingOn J ∧
        (letI : DecidableRel J.Adj := dJ;
          J.edgeFinset.card = 3 * Fintype.card V - 6) := by
  classical
  obtain ⟨J, hGJ, hJ, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension_exists__p2m_89b917c7_2895_4f7d_ae75_caac4f55b041_a1
      G hG
  let dJ : DecidableRel J.Adj := Classical.decRel _
  refine ⟨J, dJ, hGJ, hJ, ?_⟩
  exact WilliamsonShmoys.maximal_planar_drawing_has_euler_edge_count__p2m_89b917c7_2895_4f7d_ae75_caac4f55b041_a1
    J hJ hmax dJ hcard