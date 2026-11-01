-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_extension__p2m_4c00200f_eeb1_41b9_b1b1_6e3542741a6b_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:12:42.767606+00:00
-- url     : https://prove2.me/submissions/ccae1b66-09f0-4480-b923-20318fc9abef
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_extension__p2m_a05c061d_946f_411a_b5cf_34f022290b66_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_a05c061d_946f_411a_b5cf_34f022290b66_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      (∀ u v, H.Adj u v → K.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      3 * Fintype.card V = K.edgeSet.ncard + 6 := by
  obtain ⟨K, hHK, hK, hmax⟩ :=
    WilliamsonShmoys.maximal_drawable_extension__p2m_a05c061d_946f_411a_b5cf_34f022290b66_a1 H hH
  have hcount :=
    WilliamsonShmoys.maximal_planar_edge_count__p2m_a05c061d_946f_411a_b5cf_34f022290b66_a1
      K hK hCard hmax
  exact ⟨K, hHK, hK, hcount⟩