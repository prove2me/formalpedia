-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_of_maximal_planar__p2m_ffbccb21_453c_4aae_b4fb_4ee36a71a8e5_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:20:05.864318+00:00
-- url     : https://prove2.me/submissions/3a7ceb88-e8ad-40a5-874d-47411fbdd2cb

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_completion_edge_count__p2m_247de887_2f63_4fea_b543_bef5d4e212b7_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hDraw : HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hMaximal : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hHK, hKDraw, hKCount⟩ :=
    WilliamsonShmoys.exists_planar_completion_edge_count__p2m_247de887_2f63_4fea_b543_bef5d4e212b7_a2 H hDraw hV
  have hKH : K = H := hMaximal K hHK hKDraw
  rw [← hKH]
  exact hKCount
