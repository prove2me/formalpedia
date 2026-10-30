-- Prove2me | solution 1 for WilliamsonShmoys.edge_maximal_planar_drawing_has_euler_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T10:56:15.624674+00:00
-- url     : https://prove2.me/submissions/3a2f6615-4d0f-48f0-ac21-b23329266df7

import Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_drawing_triangulation_extension_for_euler_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V,
      K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K)
    (hV : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨L, hKL, hL, hcount⟩ :=
    WilliamsonShmoys.edge_maximal_planar_drawing_triangulation_extension_for_euler_count
      K hK hV
  have hLK : L ≤ K := hmax L hKL hL
  have hEq : L = K := le_antisymm hLK hKL
  simpa [hEq] using hcount