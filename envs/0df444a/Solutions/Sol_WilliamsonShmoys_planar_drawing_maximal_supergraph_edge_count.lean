-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_supergraph_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T02:09:48.125985+00:00
-- url     : https://prove2.me/submissions/955236da-ab58-4ac9-a9dd-c46172894545

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_triangulation_supergraph

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hmax : ∀ H : SimpleGraph V,
      T ≤ H →
      WilliamsonShmoys.HasPlanarDrawingOn H →
      H ≤ T) :
    T.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨H, hTH, hH, hcount⟩ :=
    WilliamsonShmoys.exists_planar_triangulation_supergraph T hV hT
  have hHT : H ≤ T := hmax H hTH hH
  have hEq : H = T := le_antisymm hHT hTH
  simpa [hEq] using hcount