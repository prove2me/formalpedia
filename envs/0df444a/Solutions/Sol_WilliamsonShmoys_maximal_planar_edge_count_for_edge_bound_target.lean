-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_for_edge_bound_target
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T08:57:32.847707+00:00
-- url     : https://prove2.me/submissions/0a6b33e7-1866-4a0f-90d8-16917fdced96

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulating_supergraph_v2

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hHK, hK, hcount⟩ :=
    WilliamsonShmoys.planar_triangulating_supergraph_v2 H hV hH
  have hKH : K = H := hmax K hHK hK
  simpa [hKH] using hcount