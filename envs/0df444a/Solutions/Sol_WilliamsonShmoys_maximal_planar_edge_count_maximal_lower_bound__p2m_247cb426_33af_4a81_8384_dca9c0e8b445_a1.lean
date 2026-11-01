-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_maximal_lower_bound__p2m_247cb426_33af_4a81_8384_dca9c0e8b445_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T20:50:37.310305+00:00
-- url     : https://prove2.me/submissions/3658537c-ed74-4a15-b4f6-08f60af4a470
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_completion__p2m_c5b64a3b_d324_45a7_86e6_d358f6728245_a2
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hmax : ∀ (J : SimpleGraph V),
      G ≤ J → WilliamsonShmoys.HasPlanarDrawingOn J → J ≤ G)
    (hcard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V - 6 ≤ G.edgeFinset.card := by
  obtain ⟨J, dJ, hGJ, hJ, hcount⟩ :=
    WilliamsonShmoys.planar_drawing_completion__p2m_c5b64a3b_d324_45a7_86e6_d358f6728245_a2
      G hG hcard
  letI : DecidableRel J.Adj := dJ
  have hJG : J ≤ G := hmax J hGJ hJ
  have hcard_le : J.edgeFinset.card ≤ G.edgeFinset.card :=
    Finset.card_le_card (SimpleGraph.edgeFinset_mono hJG)
  omega