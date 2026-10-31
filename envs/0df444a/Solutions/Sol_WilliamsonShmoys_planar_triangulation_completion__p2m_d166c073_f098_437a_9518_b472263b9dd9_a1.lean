-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_completion__p2m_d166c073_f098_437a_9518_b472263b9dd9_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:42:19.654735+00:00
-- url     : https://prove2.me/submissions/5671d7bf-b65e-4ab3-a502-753cf8e65b4e

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawable_maximal_extension__p2m_31727deb_1ab6_43dd_805b_f9cbe6cd890f_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_31727deb_1ab6_43dd_805b_f9cbe6cd890f_a1
set_option autoImplicit false

/-- Every drawable simple graph on at least three vertices has a drawable
supergraph on the same vertex type whose edge count is exactly three times the
number of vertices minus six. -/
theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (Y : SimpleGraph V)
    (hY : WilliamsonShmoys.HasPlanarDrawingOn Y)
    (hV : 3 ≤ Fintype.card V) :
    ∃ Z : SimpleGraph V, Y ≤ Z ∧
      WilliamsonShmoys.HasPlanarDrawingOn Z ∧
      Z.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨Z, hYZ, hZ, hmax⟩ :=
    WilliamsonShmoys.planar_drawable_maximal_extension__p2m_31727deb_1ab6_43dd_805b_f9cbe6cd890f_a1
      Y hY
  have hcount :=
    WilliamsonShmoys.maximal_planar_edge_count__p2m_31727deb_1ab6_43dd_805b_f9cbe6cd890f_a1
      Z hZ hV hmax
  exact ⟨Z, hYZ, hZ, hcount⟩