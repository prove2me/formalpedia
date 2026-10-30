-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_edge_count_completion_v2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T19:17:44.311021+00:00
-- url     : https://prove2.me/submissions/fe7ac091-356e-4dd8-8e3e-b4f6a3120dea

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_a3317d7a_4b18_491b_9aee_6f2b4185d855
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_a3317d7a_4b18_491b_9aee_6f2b4185d855

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hY : WilliamsonShmoys.HasPlanarDrawingOn Y)
    (hV : 3 ≤ Fintype.card V) :
    ∃ Z : SimpleGraph V,
      LE.le Y Z ∧
      WilliamsonShmoys.HasPlanarDrawingOn Z ∧
      Z.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨Z, hYZ, hZ, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph_a3317d7a_4b18_491b_9aee_6f2b4185d855 Y hY
  refine ⟨Z, hYZ, hZ, ?_⟩
  exact WilliamsonShmoys.maximal_planar_edge_count_a3317d7a_4b18_491b_9aee_6f2b4185d855 Z hZ hmax hV