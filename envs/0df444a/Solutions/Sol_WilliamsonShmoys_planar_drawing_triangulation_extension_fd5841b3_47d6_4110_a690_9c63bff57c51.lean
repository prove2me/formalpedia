-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_extension_fd5841b3_47d6_4110_a690_9c63bff57c51
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T03:43:15.094987+00:00
-- url     : https://prove2.me/submissions/46ec54a0-d754-4781-80d9-949706be6775

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_drawing_extension_fd5841b3_47d6_4110_a690_9c63bff57c51
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_fd5841b3_47d6_4110_a690_9c63bff57c51

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (hV : 3 <= Fintype.card V)
    (P : SimpleGraph V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P) :
    ∃ Q : SimpleGraph V, P ≤ Q ∧
      WilliamsonShmoys.HasPlanarDrawingOn Q ∧
      3 * Fintype.card V - 6 = Q.edgeSet.ncard := by
  obtain ⟨Q, hPQ, hQ, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_drawing_extension_fd5841b3_47d6_4110_a690_9c63bff57c51
      P hP
  exact ⟨Q, hPQ, hQ,
    WilliamsonShmoys.maximal_planar_drawing_edge_count_fd5841b3_47d6_4110_a690_9c63bff57c51
      Q hQ hV hmax⟩