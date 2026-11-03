-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_supergraph_with_triangulated_edge_count__p2m_b6ab3cff_6690_4a88_8301_64964a0bb841_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:29:09.083012+00:00
-- url     : https://prove2.me/submissions/6b49c46f-1a8e-4568-8626-f1987170872a

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_1634faf2_3284_496c_bfc9_f8ff236eda71_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_1634faf2_3284_496c_bfc9_f8ff236eda71_a1

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧
      (letI : DecidableRel L.Adj := Classical.decRel L.Adj
       letI : Fintype ↑L.edgeSet := Fintype.ofFinite _
       3 * Fintype.card V = L.edgeFinset.card + 6) := by
  classical
  obtain ⟨L, hKL, hL, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_1634faf2_3284_496c_bfc9_f8ff236eda71_a1
      K hK hV
  refine ⟨L, hKL, hL, ?_⟩
  exact WilliamsonShmoys.maximal_planar_edge_count__p2m_1634faf2_3284_496c_bfc9_f8ff236eda71_a1
    L hL hV hmax