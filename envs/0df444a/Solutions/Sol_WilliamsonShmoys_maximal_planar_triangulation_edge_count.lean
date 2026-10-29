-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_triangulation_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T01:57:17.025203+00:00
-- url     : https://prove2.me/submissions/cfd1a65d-5404-420f-bacf-0c34de6f76c8

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_supergraph

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hmax : ∀ P : SimpleGraph V, N ≤ P →
      WilliamsonShmoys.HasPlanarDrawingOn P → P = N) :
    N.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨T, hNT, hT, hcount⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_supergraph N hV hN
  have hTN : T = N := hmax T hNT hT
  simpa [hTN] using hcount