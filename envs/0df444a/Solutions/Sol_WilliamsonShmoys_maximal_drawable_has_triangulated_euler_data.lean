-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_has_triangulated_euler_data
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T06:01:49.52901+00:00
-- url     : https://prove2.me/submissions/933f9dda-ae23-4e0d-9f23-3bea82ea3514
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_WilliamsonShmoys_PlanarTriangulationEulerData
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_triangulated_extension_for_maximal_drawable_target

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K) :
    Nonempty (WilliamsonShmoys.TriangulatedSphereFaceData K) := by
  obtain ⟨L, hKL, hL, hData⟩ :=
    WilliamsonShmoys.planar_drawing_has_triangulated_extension_for_maximal_drawable_target
      K hK hCard
  have hLK : L ≤ K := hmax L hKL hL
  have hEq : L = K := le_antisymm hLK hKL
  subst L
  exact hData