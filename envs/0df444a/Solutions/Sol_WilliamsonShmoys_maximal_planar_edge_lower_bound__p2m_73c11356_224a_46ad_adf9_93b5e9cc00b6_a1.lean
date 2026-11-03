-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_73c11356_224a_46ad_adf9_93b5e9cc00b6_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:03:58.93859+00:00
-- url     : https://prove2.me/submissions/6004b4ac-3904-452d-9e04-2ea1e68ebda7

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_f2e67bcd_d844_4f8f_86df_68d56c93483a_a1
import Mathlib
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N = M)
    (hcard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V - 6 ≤ M.edgeSet.ncard := by
  obtain ⟨N, hMN, hN, hNcard⟩ :=
    WilliamsonShmoys.planar_triangulation_extension__p2m_f2e67bcd_d844_4f8f_86df_68d56c93483a_a1
      M hM hcard
  have hNM : N = M := hmax N hMN hN
  rw [hNM] at hNcard
  omega