-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_7871e1d9_1c06_462f_bc77_343c5987d399_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:52:05.710995+00:00
-- url     : https://prove2.me/submissions/153ce296-b527-4f73-bf52-3a8f49a9e17a

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_triangulated_planar_supergraph__p2m_e16fd743_6daf_4b1b_8baa_fc8319a376a6_a2

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ H : SimpleGraph V, M ≤ H → WilliamsonShmoys.HasPlanarDrawingOn H → H = M) :
    M.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨H, hMH, hHDraw, hHCount⟩ :=
    WilliamsonShmoys.triangulated_planar_supergraph__p2m_e16fd743_6daf_4b1b_8baa_fc8319a376a6_a2
      M hDraw hV
  have hEq : H = M := hMax H hMH hHDraw
  simpa [hEq] using hHCount