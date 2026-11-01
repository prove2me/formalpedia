-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_4144dd03_670b_4445_9630_6cae19c82121_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:50:52.977869+00:00
-- url     : https://prove2.me/submissions/2d3ceb52-4d1c-4c0a-b23d-19e8ff94974e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_exists_triangulated_planar_extension__p2m_96e9e482_f477_425c_819e_ee0bbf216c74_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ N : SimpleGraph V,
      (∀ u v, M.Adj u v → N.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn N →
      (∀ u v, N.Adj u v → M.Adj u v)) :
    3 * Fintype.card V = M.edgeSet.ncard + 6 := by
  apply Exists.elim
    (WilliamsonShmoys.exists_triangulated_planar_extension__p2m_96e9e482_f477_425c_819e_ee0bbf216c74_a1
      M hM hCard)
  intro H hHdata
  have hMH : ∀ u v, M.Adj u v → H.Adj u v := hHdata.1
  have hPlanar : WilliamsonShmoys.HasPlanarDrawingOn H := hHdata.2.1
  have hCount : 3 * Fintype.card V = H.edgeSet.ncard + 6 := hHdata.2.2
  have hHM : ∀ u v, H.Adj u v → M.Adj u v := hMax H hMH hPlanar
  have hEq : H = M := by
    ext u v
    exact ⟨hHM u v, hMH u v⟩
  rw [hEq] at hCount
  exact hCount