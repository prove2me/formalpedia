-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_b8a812cb_4c6a_4971_bdf9_7db1f5ebc92f_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:25:23.233808+00:00
-- url     : https://prove2.me/submissions/57ec27f2-fb95-4a12-a5a3-29de008e9386

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_d879fe2f_6575_4a1e_b2ae_694852ee5ed8_a1
import Theorems.Thm_WilliamsonShmoys_maximal_extension_edge_bound__p2m_d879fe2f_6575_4a1e_b2ae_694852ee5ed8_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N ≤ M) :
    3 * Fintype.card V ≤ M.edgeSet.ncard + 6 := by
  obtain ⟨N, hMN, hNPlanar, hNMax, hNCount⟩ :=
    WilliamsonShmoys.planar_triangulation_extension__p2m_d879fe2f_6575_4a1e_b2ae_694852ee5ed8_a1
      M hM hCard
  have hNM : N ≤ M := hMax N hMN hNPlanar
  exact WilliamsonShmoys.maximal_extension_edge_bound__p2m_d879fe2f_6575_4a1e_b2ae_694852ee5ed8_a1
    M N hMN hNM hNCount