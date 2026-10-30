-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_supergraph_edge_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T03:11:53.14602+00:00
-- url     : https://prove2.me/submissions/ed58a389-149b-4ef2-9c2d-d937578a60a4

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_extension_on_fixed_vertices
import Theorems.Thm_WilliamsonShmoys_edge_lower_bound_of_no_planar_extension_on_fixed_vertices

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ P : SimpleGraph V, N ≤ P ∧
      WilliamsonShmoys.HasPlanarDrawingOn P ∧
      3 * Fintype.card V - 6 ≤ P.edgeSet.ncard := by
  obtain ⟨P, hNP, hP, hmax⟩ :=
    WilliamsonShmoys.exists_edge_maximal_planar_extension_on_fixed_vertices N hN
  exact ⟨P, hNP, hP,
    WilliamsonShmoys.edge_lower_bound_of_no_planar_extension_on_fixed_vertices
      hV P hP hmax⟩