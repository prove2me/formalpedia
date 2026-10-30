-- Prove2me | solution 1 for WilliamsonShmoys.planar_maximal_drawing_edge_count__p2m_e311c4a7_aff6_4403_a1d3_f4a962b82e69_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:58:24.762402+00:00
-- url     : https://prove2.me/submissions/dcafdc22-1f82-4d16-a214-c8749cf798bd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_exact_edge_count_completion__p2m_105a7e64_a154_40f8_8dae_11517fa32419_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ K : SimpleGraph V,
      H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hHK, hK, hCount⟩ :=
    WilliamsonShmoys.planar_drawing_exact_edge_count_completion__p2m_105a7e64_a154_40f8_8dae_11517fa32419_a1
      H hH hV
  have hKH : K = H := hMax K hHK hK
  rw [hKH] at hCount
  exact hCount