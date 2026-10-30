-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_for_triangulation_target
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-25T23:39:17.426979+00:00
-- url     : https://prove2.me/submissions/492c7a75-26da-45f8-8bda-9bf97871760d

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_triangulation_extension

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V, H ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hHK, hK, hcount⟩ :=
    WilliamsonShmoys.exists_planar_triangulation_extension H hH hV
  have hKH : K ≤ H := hmax K hHK hK
  have hEq : H = K := le_antisymm hHK hKH
  rw [hEq]
  exact hcount