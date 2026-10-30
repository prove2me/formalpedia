-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound_completion_55e40668_6c6c_445f_853d_a7074df51c4e
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T00:39:18.02879+00:00
-- url     : https://prove2.me/submissions/2c5822da-8fbb-4e65-975a-3ea4b1218568

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_maximal_edge_augmentation

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V,
      L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L)
    (hV : 3 ≤ Fintype.card V) :
    3 * Fintype.card V - 6 ≤ L.edgeSet.ncard := by
  obtain ⟨M, hLM, hM, hcard⟩ :=
    WilliamsonShmoys.planar_maximal_edge_augmentation L hL hV
  rw [← hmax M hLM hM]
  omega