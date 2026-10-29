-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound_aca21fa1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T05:22:19.777996+00:00
-- url     : https://prove2.me/submissions/184e81dc-e2af-45b0-8092-f6fdb545140a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound_completion__p2m_b8cc851b_d85e_44da_b799_273002cb7d7c_a4
import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hCard : 3 <= Fintype.card V) :
    (G.edgeSet.ncard : Int) <= 3 * (Fintype.card V : Int) - 6 := by
  let K := Classical.choose
    (WilliamsonShmoys.planar_drawing_edge_bound_completion__p2m_b8cc851b_d85e_44da_b799_273002cb7d7c_a4 G hG hCard)
  have hprops := Classical.choose_spec
    (WilliamsonShmoys.planar_drawing_edge_bound_completion__p2m_b8cc851b_d85e_44da_b799_273002cb7d7c_a4 G hG hCard)
  have hsub : G <= K := hprops.1
  have hKcount : (K.edgeSet.ncard : Int) =
      3 * (Fintype.card V : Int) - 6 := hprops.2.2
  have hmono : G.edgeSet.ncard <= K.edgeSet.ncard :=
    Set.ncard_mono (SimpleGraph.edgeSet_mono hsub)
  calc
    (G.edgeSet.ncard : Int) <= (K.edgeSet.ncard : Int) := by
      exact_mod_cast hmono
    _ = 3 * (Fintype.card V : Int) - 6 := hKcount