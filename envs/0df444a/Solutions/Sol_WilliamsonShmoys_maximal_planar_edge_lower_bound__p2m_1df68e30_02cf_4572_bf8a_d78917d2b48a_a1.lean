-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_1df68e30_02cf_4572_bf8a_d78917d2b48a_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:19:42.858558+00:00
-- url     : https://prove2.me/submissions/8bb31722-e20c-4ead-8bb6-49baaf04e804
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_augmentation_lower_bound__p2m_99986598_6392_4501_ac0d_a0cd3c835fd3_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ K : SimpleGraph V, L ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = L) :
    3 * Fintype.card V - 6 ≤ L.edgeSet.ncard := by
  obtain ⟨K, hLK, hK, hbound⟩ :=
    WilliamsonShmoys.planar_edge_augmentation_lower_bound__p2m_99986598_6392_4501_ac0d_a0cd3c835fd3_a1
      L hcard hL
  have hEq : K = L := hmax K hLK hK
  rw [hEq] at hbound
  exact hbound