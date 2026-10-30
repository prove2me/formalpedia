-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_bcd4e9c3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T00:40:23.902727+00:00
-- url     : https://prove2.me/submissions/f8e98478-c658-4578-9aa5-cf586c06c2d3

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_with_triangulation_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨L, hKL, hL, hcount⟩ :=
    WilliamsonShmoys.planar_supergraph_with_triangulation_count K hV hK
  have hLK : L = K := hmax L hKL hL
  simpa [hLK] using hcount