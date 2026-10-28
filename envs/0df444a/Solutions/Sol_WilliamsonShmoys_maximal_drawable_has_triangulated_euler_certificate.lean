-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_has_triangulated_euler_certificate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T14:21:13.745453+00:00
-- url     : https://prove2.me/submissions/1139c007-7f86-455d-90c7-fcef9a615214
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_drawable_graph_has_triangular_euler_supergraph

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hU : WilliamsonShmoys.HasPlanarDrawingOn U)
    (hmax : ∀ X : SimpleGraph V,
      U ≤ X → WilliamsonShmoys.HasPlanarDrawingOn X → X = U) :
    WilliamsonShmoys.HasTriangularEulerCertificate U := by
  obtain ⟨X, hUX, hX, hcert⟩ :=
    WilliamsonShmoys.drawable_graph_has_triangular_euler_supergraph U hV hU
  have hEq : X = U := hmax X hUX hX
  simpa [hEq] using hcert
