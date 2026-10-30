-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_e696380b
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T07:02:07.014276+00:00
-- url     : https://prove2.me/submissions/4f2d9213-4368-461e-be36-50b2f0bdc1d6

import Theorems.Thm_WilliamsonShmoys_maximal_planar_extension_edge_count

set_option autoImplicit false

 theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ H : SimpleGraph V,
      K ≤ H → WilliamsonShmoys.HasPlanarDrawingOn H → H = K) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨H, hKH, hH, hcount⟩ :=
    WilliamsonShmoys.maximal_planar_extension_edge_count K hV hK
  have hEq : H = K := hmax H hKH hH
  simpa [hEq] using hcount