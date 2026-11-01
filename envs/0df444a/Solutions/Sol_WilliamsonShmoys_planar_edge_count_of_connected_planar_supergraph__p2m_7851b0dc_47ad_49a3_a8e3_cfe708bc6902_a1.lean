-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_of_connected_planar_supergraph__p2m_7851b0dc_47ad_49a3_a8e3_cfe708bc6902_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:25:16.448997+00:00
-- url     : https://prove2.me/submissions/ab554f6a-a636-41b0-89a4-254872fffd1b

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hconnBound : ∀ (H : SimpleGraph V) (dH : DecidableRel H.Adj),
      H.Connected → HasPlanarDrawingOn H → 3 ≤ Fintype.card V →
      (letI : DecidableRel H.Adj := dH
       H.edgeFinset.card ≤ 3 * Fintype.card V - 6))
    (hG : HasPlanarDrawingOn G)
    (hcard : 3 ≤ Fintype.card V)
    (hcomplete : ∃ (H : SimpleGraph V) (dH : DecidableRel H.Adj),
      G ≤ H ∧ H.Connected ∧ HasPlanarDrawingOn H) :
    (letI : DecidableRel G.Adj := dG
     G.edgeFinset.card ≤ 3 * Fintype.card V - 6) := by
  letI : DecidableRel G.Adj := dG
  rcases hcomplete with ⟨H, dH, hGH, hHconn, hHplanar⟩
  letI : DecidableRel H.Adj := dH
  have hHbound := hconnBound H dH hHconn hHplanar hcard
  have hEdges : G.edgeFinset ⊆ H.edgeFinset :=
    (SimpleGraph.edgeFinset_subset_edgeFinset).2 hGH
  exact (Finset.card_le_card hEdges).trans hHbound