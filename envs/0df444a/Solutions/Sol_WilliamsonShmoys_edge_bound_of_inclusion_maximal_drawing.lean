-- Prove2me | solution 1 for WilliamsonShmoys.edge_bound_of_inclusion_maximal_drawing
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T02:16:22.846801+00:00
-- url     : https://prove2.me/submissions/60edd7dc-d531-45e3-984b-f9f71149901b

import Theorems.Thm_WilliamsonShmoys_planar_completion_with_edge_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn K →
      K.edgeSet = H.edgeSet) :
    3 * Fintype.card V ≤ H.edgeSet.ncard + 6 := by
  obtain ⟨K, hHK, hK, hcount⟩ :=
    WilliamsonShmoys.planar_completion_with_edge_count H hV hH
  have hEq : K.edgeSet = H.edgeSet := hmax K hHK hK
  have hEqCount : 3 * Fintype.card V = H.edgeSet.ncard + 6 := by
    simpa [hEq] using hcount
  exact le_of_eq hEqCount
