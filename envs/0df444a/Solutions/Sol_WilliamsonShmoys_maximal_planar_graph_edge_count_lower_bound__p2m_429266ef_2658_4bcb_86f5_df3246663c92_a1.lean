-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count_lower_bound__p2m_429266ef_2658_4bcb_86f5_df3246663c92_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:35:28.175795+00:00
-- url     : https://prove2.me/submissions/c6f576f6-a105-4bb0-92c7-3e573b76fbbd

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_triangulation_extension__p2m_5b8e7ffd_8a89_4dff_8c54_ba70a4e1be67_a1

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (Z : SimpleGraph V)
    (hZ : WilliamsonShmoys.HasPlanarDrawingOn Z)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ W : SimpleGraph V, Z ≤ W →
      WilliamsonShmoys.HasPlanarDrawingOn W → W = Z) :
    3 * Fintype.card V - 6 ≤ Z.edgeSet.ncard := by
  obtain ⟨W, hZW, hW, hcard⟩ :=
    WilliamsonShmoys.exists_planar_triangulation_extension__p2m_5b8e7ffd_8a89_4dff_8c54_ba70a4e1be67_a1
      Z hZ hV
  have hWZ : W = Z := hmax W hZW hW
  rw [hWZ] at hcard
  exact hcard.ge