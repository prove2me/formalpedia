-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_e4274472_fa7f_45c2_bc46_56de2add020a_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T20:50:05.287731+00:00
-- url     : https://prove2.me/submissions/08da1676-9f7d-47b7-aab4-f521af8dd155
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_maximal_extension__p2m_1479c9f9_4504_425f_aa40_f345c4f3c928_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_1479c9f9_4504_425f_aa40_f345c4f3c928_a2

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hmax : forall K : SimpleGraph V, H <= K -> HasPlanarDrawingOn K -> K = H)
    (hcard : 3 <= Fintype.card V) :
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj;
      3 * Fintype.card V - 6 <= H.edgeFinset.card) := by
  classical
  obtain ⟨K, hHK, hK, hKmax⟩ :=
    WilliamsonShmoys.planar_maximal_extension__p2m_1479c9f9_4504_425f_aa40_f345c4f3c928_a2 H hH
  have hEq : K = H := hmax K hHK hK
  subst K
  have hEdges :=
    WilliamsonShmoys.maximal_planar_edge_count__p2m_1479c9f9_4504_425f_aa40_f345c4f3c928_a2
      H hK hKmax hcard
  exact le_of_eq hEdges