-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_ea40f167_79e5_4439_8a7d_ae09e117fb58_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:47:10.455605+00:00
-- url     : https://prove2.me/submissions/0b91f4f8-e60c-405a-b450-2cb317c0ff02

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_triangulation_extension__p2m_f9467e46_2ce6_4b9f_b76a_966f262664e2_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ L.edgeSet.ncard + 6 := by
  obtain ⟨M, hLM, hMPlanar, hCount⟩ :=
    WilliamsonShmoys.maximal_planar_triangulation_extension__p2m_f9467e46_2ce6_4b9f_b76a_966f262664e2_a1
      L hL hCard
  have hML : M = L := hMax M hLM hMPlanar
  rw [← hML]
  exact hCount.le