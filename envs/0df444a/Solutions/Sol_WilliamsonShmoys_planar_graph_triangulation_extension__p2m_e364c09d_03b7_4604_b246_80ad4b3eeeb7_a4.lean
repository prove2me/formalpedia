-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_triangulation_extension__p2m_e364c09d_03b7_4604_b246_80ad4b3eeeb7_a4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:12:12.340908+00:00
-- url     : https://prove2.me/submissions/6c94e889-b551-42af-a072-3c43b3e77a9b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_exists__p2m_8b952692_ce82_4b1a_b285_daef0e717378_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_8b952692_ce82_4b1a_b285_daef0e717378_a1
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      (letI : DecidableRel K.Adj := Classical.decRel K.Adj;
       K.edgeFinset.card + 6 = 3 * Fintype.card V) := by
  classical
  obtain ⟨K, hHK, hK, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension_exists__p2m_8b952692_ce82_4b1a_b285_daef0e717378_a1
      H hH hcard
  refine ⟨K, hHK, hK, ?_⟩
  exact WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_8b952692_ce82_4b1a_b285_daef0e717378_a1
    K hK hmax hcard