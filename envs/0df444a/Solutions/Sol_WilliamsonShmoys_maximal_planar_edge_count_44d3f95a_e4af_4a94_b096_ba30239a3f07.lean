-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_44d3f95a_e4af_4a94_b096_ba30239a3f07
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T16:42:31.032985+00:00
-- url     : https://prove2.me/submissions/22670886-cdb7-4546-9d74-5892d0bdda3b

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound_c9504d43_439f_48f5_9c1d_7c90f019cbdd
import Theorems.Thm_WilliamsonShmoys_planar_drawable_extension_c9504d43_439f_48f5_9c1d_7c90f019cbdd

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hMax : ∀ K : SimpleGraph V,
      H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hupper : H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
    WilliamsonShmoys.planar_drawing_edge_bound_c9504d43_439f_48f5_9c1d_7c90f019cbdd H hV hH
  have hnotlt : ¬ H.edgeSet.ncard + 6 < 3 * Fintype.card V := by
    intro hlt
    obtain ⟨K, hHK, hnotKH, hK⟩ :=
      WilliamsonShmoys.planar_drawable_extension_c9504d43_439f_48f5_9c1d_7c90f019cbdd H hV hH hlt
    exact hnotKH (hMax K hHK hK)
  exact Nat.le_antisymm hupper (Nat.le_of_not_gt hnotlt)