-- Prove2me | solution 1 for WilliamsonShmoys.exists_edge_maximal_planar_supergraph__p2m_d8025907_d5c3_4b74_a462_234358441f90_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:50:31.153555+00:00
-- url     : https://prove2.me/submissions/d98b3d6f-b267-473d-b56b-008aa4bf4838

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_for_finite_graph_property__p2m_c7b07ed7_db7c_450f_a64f_c5e3047d491b_a1
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    Exists fun (L : SimpleGraph V) => Exists fun (dL : DecidableRel L.Adj) =>
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      K.edgeFinset ⊆ L.edgeFinset ∧
      (∀ (M : SimpleGraph V) (dM : DecidableRel M.Adj),
        WilliamsonShmoys.HasPlanarDrawingOn M →
        L.edgeFinset ⊆ M.edgeFinset → M.edgeFinset = L.edgeFinset) := by
  classical
  obtain ⟨L, hL, hKL, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_supergraph_for_finite_graph_property__p2m_c7b07ed7_db7c_450f_a64f_c5e3047d491b_a1
      K WilliamsonShmoys.HasPlanarDrawingOn hK
  refine ⟨L, Classical.decRel L.Adj, hL, ?_, ?_⟩
  · exact SimpleGraph.edgeFinset_subset_edgeFinset.mpr hKL
  · intro M dM hM hLM
    have hLM' : L ≤ M := SimpleGraph.edgeFinset_subset_edgeFinset.mp hLM
    have hEq : M = L := hmax M hM hLM'
    simpa [SimpleGraph.edgeFinset_inj] using hEq