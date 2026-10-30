-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_has_triangulated_supergraph_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T07:18:25.842896+00:00
-- url     : https://prove2.me/submissions/66774ee8-f74c-4b80-9796-56342e3497bc

import Mathlib.Tactic
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_for_edge_count_6274f47d_124c_4fd1_84e6_71540a951a1f
import Theorems.Thm_WilliamsonShmoys_maximal_planar_face_decomposition_for_edge_count_6274f47d_124c_4fd1_84e6_71540a951a1f
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hPlanar : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hHK, hKPlanar, hMax⟩ :=
    WilliamsonShmoys.maximal_planar_supergraph_for_edge_count_6274f47d_124c_4fd1_84e6_71540a951a1f H hPlanar
  obtain ⟨f, hEuler, hFaces⟩ :=
    WilliamsonShmoys.maximal_planar_face_decomposition_for_edge_count_6274f47d_124c_4fd1_84e6_71540a951a1f
      K hKPlanar hMax hCard
  refine ⟨K, hHK, hKPlanar, ?_⟩
  omega