-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_has_triangulated_extension__p2m_055aa8e4_db8a_47ed_b733_513d02bcef62_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:01:39.599897+00:00
-- url     : https://prove2.me/submissions/acd715c0-2dec-41f1-b949-996390a37779
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph__p2m_3a1649bb_b908_4400_8c80_435b14739a2c_a1
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count__p2m_3a1649bb_b908_4400_8c80_435b14739a2c_a1

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V,
      H.edgeSet ⊆ N.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      N.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨N, hHN, hN, hMax⟩ :=
    WilliamsonShmoys.exists_maximal_drawable_supergraph__p2m_3a1649bb_b908_4400_8c80_435b14739a2c_a1
      H hH
  exact ⟨N, hHN, hN,
    WilliamsonShmoys.maximal_drawable_edge_count__p2m_3a1649bb_b908_4400_8c80_435b14739a2c_a1
      N hCard hN hMax⟩