-- Prove2me | solution 1 for WilliamsonShmoys.exists_triangulated_planar_extension__p2m_96e9e482_f477_425c_819e_ee0bbf216c74_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:53:28.35975+00:00
-- url     : https://prove2.me/submissions/87cdb70e-8ca8-405b-8b39-982d68d9218e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_extension__p2m_1345f058_46fd_4b3f_bd68_5a032464e223_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_1345f058_46fd_4b3f_bd68_5a032464e223_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      (∀ u v, G.Adj u v → H.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      3 * Fintype.card V = H.edgeSet.ncard + 6 := by
  obtain ⟨H, hGH, hH, hMax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_extension__p2m_1345f058_46fd_4b3f_bd68_5a032464e223_a1
      G hG hCard
  exact ⟨H, hGH, hH,
    WilliamsonShmoys.maximal_planar_edge_count__p2m_1345f058_46fd_4b3f_bd68_5a032464e223_a1
      H hH hCard hMax⟩