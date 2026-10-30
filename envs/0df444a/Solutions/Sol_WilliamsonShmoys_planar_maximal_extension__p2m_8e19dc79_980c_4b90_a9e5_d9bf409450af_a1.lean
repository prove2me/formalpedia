-- Prove2me | solution 1 for WilliamsonShmoys.planar_maximal_extension__p2m_8e19dc79_980c_4b90_a9e5_d9bf409450af_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:37:34.906298+00:00
-- url     : https://prove2.me/submissions/c7d05ed8-2e87-4cd3-ad74-0f8dddec8b74

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_graph_property_has_maximal_extension__p2m_4274c3cc_8877_4dcd_9fb0_968a87bc56a7_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hDraw : HasPlanarDrawingOn K) : ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧ ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L := by
  exact WilliamsonShmoys.finite_graph_property_has_maximal_extension__p2m_4274c3cc_8877_4dcd_9fb0_968a87bc56a7_a1
    (P := fun G : SimpleGraph V => HasPlanarDrawingOn G) K hDraw