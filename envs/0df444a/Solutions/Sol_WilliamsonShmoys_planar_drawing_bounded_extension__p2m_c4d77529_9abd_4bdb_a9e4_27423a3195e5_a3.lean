-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_bounded_extension__p2m_c4d77529_9abd_4bdb_a9e4_27423a3195e5_a3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:38:07.008041+00:00
-- url     : https://prove2.me/submissions/0e9fce35-03da-433e-a18f-aef4730d19dc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_maximal_extension__p2m_0217dacd_29f2_4bf3_8012_06725ffda067_a2
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_bounds__p2m_0217dacd_29f2_4bf3_8012_06725ffda067_a5

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj;
     ∃ K : SimpleGraph V, H ≤ K ∧
       WilliamsonShmoys.HasPlanarDrawingOn K ∧
       (letI : DecidableRel K.Adj := Classical.decRel K.Adj;
        H.edgeFinset.card ≤ K.edgeFinset.card ∧
        Fintype.card V ≤ K.edgeFinset.card + 2 ∧
        K.edgeFinset.card ≤ 3 * Fintype.card V - 6)) := by
  classical
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  rcases WilliamsonShmoys.drawable_maximal_extension__p2m_0217dacd_29f2_4bf3_8012_06725ffda067_a2
      H hH with ⟨K, hHK, hK, hmax⟩
  letI : DecidableRel K.Adj := Classical.decRel K.Adj
  have hbounds :=
    WilliamsonShmoys.maximal_drawable_edge_bounds__p2m_0217dacd_29f2_4bf3_8012_06725ffda067_a5
      H K hHK hcard hK hmax
  exact ⟨K, hHK, hK, hbounds.1, hbounds.2.1, hbounds.2.2⟩
