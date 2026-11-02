-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_exact_edge_count__p2m_db3907fa_cf67_46ea_9385_43b8ffa0c261_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:42:44.958911+00:00
-- url     : https://prove2.me/submissions/1edcf826-6835-4247-bd74-d7c255a0ffb1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_has_triangulated_extension__p2m_055aa8e4_db8a_47ed_b733_513d02bcef62_a1
import Mathlib

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ N : SimpleGraph V,
      H.edgeSet ⊆ N.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn N →
      N.edgeSet ⊆ H.edgeSet) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨N, hHN, hN, hNcard⟩ :=
    WilliamsonShmoys.maximal_planar_drawing_has_triangulated_extension__p2m_055aa8e4_db8a_47ed_b733_513d02bcef62_a1
      H hH hCard
  have hNH : N.edgeSet ⊆ H.edgeSet := hMax N hHN hN
  have hEq : H.edgeSet = N.edgeSet := Set.Subset.antisymm hHN hNH
  rw [hEq]
  exact hNcard