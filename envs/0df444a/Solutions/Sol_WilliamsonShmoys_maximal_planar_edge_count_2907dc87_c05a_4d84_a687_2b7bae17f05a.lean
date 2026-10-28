-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_2907dc87_c05a_4d84_a687_2b7bae17f05a
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T00:22:23.595308+00:00
-- url     : https://prove2.me/submissions/df928bd5-16e0-4605-ba0f-85377e8a4e89
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_maximal_extension_a4893b45
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_a4893b45

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ K : SimpleGraph V, H ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hHK, hK, hSat⟩ :=
    WilliamsonShmoys.planar_maximal_extension_a4893b45 H hH
  have hKH : K = H := hMax K hHK hK
  have hCount :=
    WilliamsonShmoys.maximal_planar_edge_count_a4893b45 K hK hV hSat
  rw [← hKH]
  exact hCount