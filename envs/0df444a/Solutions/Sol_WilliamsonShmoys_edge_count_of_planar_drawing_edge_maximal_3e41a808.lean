-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_of_planar_drawing_edge_maximal_3e41a808
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T02:25:53.633704+00:00
-- url     : https://prove2.me/submissions/f84c03c3-5c40-41b2-bc45-99343e373102

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_edge_count_3v_minus_6

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V,
      H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → H = K) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hHK, hK, hcount⟩ :=
    WilliamsonShmoys.planar_supergraph_edge_count_3v_minus_6 H hV hH
  have hEq : H = K := hmax K hHK hK
  simpa [hEq] using hcount