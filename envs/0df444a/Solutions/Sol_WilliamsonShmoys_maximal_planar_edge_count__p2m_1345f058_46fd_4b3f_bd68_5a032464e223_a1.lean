-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_1345f058_46fd_4b3f_bd68_5a032464e223_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:02:34.256256+00:00
-- url     : https://prove2.me/submissions/07637417-b480-456f-bd03-67977116da8e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_4c00200f_eeb1_41b9_b1b1_6e3542741a6b_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ K : SimpleGraph V,
      (∀ u v, H.Adj u v → K.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn K →
      ∀ u v, K.Adj u v → H.Adj u v) :
    3 * Fintype.card V = H.edgeSet.ncard + 6 := by
  obtain ⟨K, hHK, hK, hCount⟩ :=
    WilliamsonShmoys.planar_triangulation_extension__p2m_4c00200f_eeb1_41b9_b1b1_6e3542741a6b_a1 H hH hCard
  have hKH : ∀ u v, K.Adj u v → H.Adj u v := hMax K hHK hK
  have hEq : K = H := by
    ext u v
    exact ⟨hKH u v, hHK u v⟩
  rw [hEq] at hCount
  exact hCount