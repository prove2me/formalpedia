-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count_for_triangulated_face_data
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T15:22:53.154375+00:00
-- url     : https://prove2.me/submissions/a833a770-2baf-4a18-af25-2f71cb7a2752

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_edge_count_completion

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : forall K : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn K -> H <= K -> K <= H)
    (hV : 3 <= Fintype.card V) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hHK, hK, hcount⟩ :=
    WilliamsonShmoys.exists_planar_edge_count_completion H hH hV
  have hKH : K <= H := hmax K hK hHK
  have heq : H = K := le_antisymm hHK hKH
  rw [heq]
  exact hcount