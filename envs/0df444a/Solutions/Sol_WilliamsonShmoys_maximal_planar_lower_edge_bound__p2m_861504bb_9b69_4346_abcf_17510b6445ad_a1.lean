-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_lower_edge_bound__p2m_861504bb_9b69_4346_abcf_17510b6445ad_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:11:35.932688+00:00
-- url     : https://prove2.me/submissions/66a1d62b-42ee-4ca1-953b-adf1012036a6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_augmentation_to_triangulation__p2m_0448f4f3_6535_4d82_8dda_cbfbd113fe3f_a2
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hcard : 3 <= Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hmax : forall K : SimpleGraph V,
      G <= K -> WilliamsonShmoys.HasPlanarDrawingOn K -> K <= G) :
    (letI : DecidableRel G.Adj := Classical.decRel G.Adj
     3 * Fintype.card V - 6 <= G.edgeFinset.card) := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  obtain ⟨K, hGK, hK, htri⟩ :=
    WilliamsonShmoys.planar_drawing_augmentation_to_triangulation__p2m_0448f4f3_6535_4d82_8dda_cbfbd113fe3f_a2
      G hcard hG
  have hKG : K = G := le_antisymm (hmax K hGK hK) hGK
  subst K
  have htri' : G.edgeFinset.card = 3 * Fintype.card V - 6 := by
    simpa using htri
  omega