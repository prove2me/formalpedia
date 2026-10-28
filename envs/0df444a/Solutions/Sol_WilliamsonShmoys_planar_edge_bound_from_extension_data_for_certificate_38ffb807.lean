-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_bound_from_extension_data_for_certificate_38ffb807
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T13:25:09.817694+00:00
-- url     : https://prove2.me/submissions/4891fcc8-57f0-43a9-8bd4-11e80314784a

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hext : ∃ H : SimpleGraph V, K ≤ H ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H)
    (hconnBound : ∀ (G : SimpleGraph V), 3 ≤ Fintype.card V → G.Connected →
      WilliamsonShmoys.HasPlanarDrawingOn G →
      G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  rcases hext with ⟨H, hKH, hHconn, hHdraw⟩
  have hsub : K.edgeSet ⊆ H.edgeSet := SimpleGraph.edgeSet_mono hKH
  have hcard : K.edgeSet.ncard ≤ H.edgeSet.ncard :=
    Set.ncard_le_ncard hsub (Set.toFinite _)
  have hbound := hconnBound H hV hHconn hHdraw
  omega