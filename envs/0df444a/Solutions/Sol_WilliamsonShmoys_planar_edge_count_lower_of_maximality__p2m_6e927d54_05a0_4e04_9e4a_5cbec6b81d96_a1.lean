-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_lower_of_maximality__p2m_6e927d54_05a0_4e04_9e4a_5cbec6b81d96_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:51:55.757334+00:00
-- url     : https://prove2.me/submissions/40fd5516-ebd8-40b1-b531-e8d7c5788ee0

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension__p2m_71bf5396_ae49_4e3b_9478_7acac339f298_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (hT : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hcard : 3 <= Fintype.card V)
    (hmax : forall U : SimpleGraph V, T <= U ->
      WilliamsonShmoys.HasPlanarDrawingOn U -> U = T) :
    letI : DecidableRel T.Adj := Classical.decRel T.Adj
    3 * Fintype.card V <= T.edgeFinset.card + 6 := by
  classical
  obtain ⟨U, hTU, hU, hcount⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_71bf5396_ae49_4e3b_9478_7acac339f298_a1
      T hT hcard
  have hUT : U = T := hmax U hTU hU
  subst U
  exact hcount.le
