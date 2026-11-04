-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_bound_from_connected_induced_bounds__p2m_ac18a95b_13f8_4a76_980e_021bef74dbe9_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:41:01.478205+00:00
-- url     : https://prove2.me/submissions/e21346da-3b23-40be-9584-dfdabd809543

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_bound_connected_case__p2m_d560826c_2a6b_46ec_826e_191525151789_a1
import Theorems.Thm_WilliamsonShmoys_planar_edge_bound_disconnected_case__p2m_d560826c_2a6b_46ec_826e_191525151789_a1
import Mathlib
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (dN : DecidableRel N.Adj)
    (hcard : 3 <= Fintype.card V)
    (hlocal : ∀ s : Finset V, 3 <= s.card →
      (N.induce (s : Set V)).Connected →
      (N.induce (s : Set V)).edgeFinset.card <= 3 * s.card - 6) :
    N.edgeFinset.card <= 3 * Fintype.card V - 6 := by
  by_cases hc : N.Connected
  · exact WilliamsonShmoys.planar_edge_bound_connected_case__p2m_d560826c_2a6b_46ec_826e_191525151789_a1
      N dN hcard hlocal hc
  · exact WilliamsonShmoys.planar_edge_bound_disconnected_case__p2m_d560826c_2a6b_46ec_826e_191525151789_a1
      N dN hcard hlocal hc