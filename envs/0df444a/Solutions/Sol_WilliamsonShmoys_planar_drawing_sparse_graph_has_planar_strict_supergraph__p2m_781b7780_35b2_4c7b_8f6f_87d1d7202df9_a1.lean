-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_sparse_graph_has_planar_strict_supergraph__p2m_781b7780_35b2_4c7b_8f6f_87d1d7202df9_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T18:34:30.72574+00:00
-- url     : https://prove2.me/submissions/c1394511-0252-45c0-8106-61f0b2b98f7e

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_maximal_planar_supergraph__p2m_7e1e673f_b342_4c9b_bd1e_cc03f8c5f53a_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_bound__p2m_7e1e673f_b342_4c9b_bd1e_cc03f8c5f53a_a2

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hCard : 3 <= Fintype.card V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hSparse : T.edgeSet.ncard < 3 * Fintype.card V - 6) :
    ∃ R : SimpleGraph V,
      (∀ u v, T.Adj u v → R.Adj u v) ∧
      R ≠ T ∧
      WilliamsonShmoys.HasPlanarDrawingOn R := by
  obtain ⟨R, hTR, hMax, hR⟩ :=
    WilliamsonShmoys.finite_maximal_planar_supergraph__p2m_7e1e673f_b342_4c9b_bd1e_cc03f8c5f53a_a2 T hT
  refine ⟨R, hTR, ?_, hR⟩
  intro hEq
  subst R
  have hBound :=
    WilliamsonShmoys.maximal_planar_graph_edge_bound__p2m_7e1e673f_b342_4c9b_bd1e_cc03f8c5f53a_a2
      T hCard hT hMax
  omega