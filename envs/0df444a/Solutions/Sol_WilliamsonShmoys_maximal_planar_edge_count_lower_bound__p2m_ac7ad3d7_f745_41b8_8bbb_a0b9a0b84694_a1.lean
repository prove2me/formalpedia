-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_ac7ad3d7_f745_41b8_8bbb_a0b9a0b84694_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:18:16.292419+00:00
-- url     : https://prove2.me/submissions/d3e15065-e3e6-4d9d-ba41-f0411f2d0911

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_augmentation_edge_count__p2m_05a50faf_c208_4b89_a21d_3d6ee49fb52f_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hcard : 3 <= Fintype.card V)
    (hmax : ∀ L : SimpleGraph V,
      G ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = G) :
    3 * Fintype.card V - 6 <= G.edgeSet.ncard := by
  obtain ⟨H, hGH, hHplanar, hcount⟩ :=
    WilliamsonShmoys.planar_augmentation_edge_count__p2m_05a50faf_c208_4b89_a21d_3d6ee49fb52f_a1
      G hplanar hcard
  have hEq : H = G := hmax H hGH hHplanar
  rw [← hEq]
  exact le_of_eq hcount