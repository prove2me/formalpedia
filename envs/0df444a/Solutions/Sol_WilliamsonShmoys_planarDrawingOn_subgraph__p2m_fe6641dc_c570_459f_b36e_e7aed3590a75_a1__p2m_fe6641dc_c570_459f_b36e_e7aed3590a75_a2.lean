-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawingOn_subgraph__p2m_fe6641dc_c570_459f_b36e_e7aed3590a75_a1__p2m_fe6641dc_c570_459f_b36e_e7aed3590a75_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T20:46:24.448213+00:00
-- url     : https://prove2.me/submissions/81213313-a170-446d-aee5-13d36e2cbaf2

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    {G H : SimpleGraph V}
    (hGH : G.edgeSet ⊆ H.edgeSet)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    WilliamsonShmoys.HasPlanarDrawingOn G := by
  rcases hH with ⟨p, arc, hp, hedge, hcross⟩
  refine ⟨p, arc, hp, ?_, ?_⟩
  · intro u v huv hadj
    have hadjH : H.Adj u v := by
      apply H.mem_edgeSet.mp
      exact hGH (G.mem_edgeSet.mpr hadj)
    exact hedge u v huv hadjH
  · intro u v x y huv hxy hadjG hadjG' hne t ht s hs heq
    have hadjH : H.Adj u v := by
      apply H.mem_edgeSet.mp
      exact hGH (G.mem_edgeSet.mpr hadjG)
    have hadjH' : H.Adj x y := by
      apply H.mem_edgeSet.mp
      exact hGH (G.mem_edgeSet.mpr hadjG')
    exact hcross u v x y huv hxy hadjH hadjH' hne t ht s hs heq