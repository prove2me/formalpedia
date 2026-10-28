-- Prove2me | solution 1 for WilliamsonShmoys.iterate_bridge_extensions
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-25T23:30:35.583694+00:00
-- url     : https://prove2.me/submissions/3a61b9a1-3c41-45f9-95c2-be10d163f237

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_simpleGraph_maximal_extension
import Theorems.Thm_WilliamsonShmoys_maximal_extension_connected

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (bridge_extension : ∀ (J : SimpleGraph V),
      WilliamsonShmoys.HasPlanarDrawingOn J →
      ¬ (∀ u v : V, Nonempty (J.Walk u v)) →
      ∃ L : SimpleGraph V,
        J ≤ L ∧
        WilliamsonShmoys.HasPlanarDrawingOn L ∧
        ∃ u v : V, ¬ Nonempty (J.Walk u v) ∧ L.Adj u v) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧
      (∀ u v : V, Nonempty (H.Walk u v)) ∧
      WilliamsonShmoys.HasPlanarDrawingOn H := by
  obtain ⟨H, hKH, hH, hmax⟩ :=
    WilliamsonShmoys.finite_simpleGraph_maximal_extension K
      WilliamsonShmoys.HasPlanarDrawingOn hK
  have hconnected :=
    WilliamsonShmoys.maximal_extension_connected H
      WilliamsonShmoys.HasPlanarDrawingOn hH hmax bridge_extension
  exact ⟨H, hKH, hconnected, hH⟩