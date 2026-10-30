-- Prove2me | solution 1 for WilliamsonShmoys.planar_maximal_drawable_graph_edge_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T17:21:25.170419+00:00
-- url     : https://prove2.me/submissions/577828d6-c42f-41c3-97e5-cb24ac72ac06

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_has_triangulated_face_count

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hR : WilliamsonShmoys.HasPlanarDrawingOn R)
    (hmax : ∀ T : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn T →
      R ≤ T → T = R)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V - 6 ≤ R.edgeSet.ncard := by
  obtain ⟨f, hEuler, hFaceIncidence⟩ :=
    WilliamsonShmoys.maximal_drawable_graph_has_triangulated_face_count
      R hR hmax hCard
  omega