-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_extension_density_8b6262cf
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T07:45:52.971875+00:00
-- url     : https://prove2.me/submissions/ee20b436-abc5-48dc-b7cc-69cfc5577d29

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_extension_density_augmentation

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ H : SimpleGraph V,
      L.edgeSet ⊆ H.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn H →
      L.edgeSet = H.edgeSet) :
    3 * Fintype.card V - 6 ≤ L.edgeSet.ncard := by
  obtain ⟨H, hsub, hH, hbound⟩ :=
    WilliamsonShmoys.maximal_planar_extension_density_augmentation L hL hV
  rw [← hmax H hsub hH] at hbound
  exact hbound