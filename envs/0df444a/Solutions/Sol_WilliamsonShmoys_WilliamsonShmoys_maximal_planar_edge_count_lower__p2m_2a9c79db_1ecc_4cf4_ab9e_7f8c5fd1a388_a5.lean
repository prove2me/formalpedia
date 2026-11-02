-- Prove2me | solution 1 for WilliamsonShmoys.WilliamsonShmoys_maximal_planar_edge_count_lower__p2m_2a9c79db_1ecc_4cf4_ab9e_7f8c5fd1a388_a5
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T11:46:08.249846+00:00
-- url     : https://prove2.me/submissions/2ae3a6e7-327e-40e7-a8ab-22a37380d30b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_augmentation__p2m_2ea99569_5736_493f_8895_a821efa27469_a1
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hG : HasPlanarDrawingOn G)
    (hmax : forall R : SimpleGraph V, G <= R -> HasPlanarDrawingOn R -> R <= G) :
    letI : DecidableRel G.Adj := Classical.decRel G.Adj
    3 * Fintype.card V <= G.edgeFinset.card + 6 := by
  classical
  obtain ⟨R, hGR, hR, hEdges⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_augmentation__p2m_2ea99569_5736_493f_8895_a821efa27469_a1
      G hV hG
  have hRG : R ≤ G := hmax R hGR hR
  have hEq : R = G := le_antisymm hRG hGR
  subst R
  exact le_of_eq hEdges