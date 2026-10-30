-- Prove2me | solution 1 for WilliamsonShmoys.planar_maximal_extension__p2m_3662a54d_ea7a_4ea3_804a_c2f8a32e2408_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:59:33.795151+00:00
-- url     : https://prove2.me/submissions/712a26d2-9d2d-49c6-b98d-27ab2ba15eab

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hconn : G.Connected)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.Connected ∧
      (∀ K : SimpleGraph V,
        H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H) ∧
      G.edgeSet.ncard ≤ H.edgeSet.ncard := by
  classical
  let candidates : Set (SimpleGraph V) :=
    {H | G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H}
  have hfinite : candidates.Finite := Set.toFinite candidates
  have hnonempty : candidates.Nonempty := ⟨G, le_rfl, hG⟩
  obtain ⟨H, hmax⟩ := hfinite.exists_maximal hnonempty
  have hHCandidate : candidates H := hmax.1
  have hGH : G ≤ H := hHCandidate.1
  refine ⟨H, hGH, hHCandidate.2, hconn.mono hGH, ?_, ?_⟩
  · intro K hHK hKplanar
    exact hmax.2 ⟨hGH.trans hHK, hKplanar⟩ hHK
  · have hEdges : G.edgeSet ⊆ H.edgeSet := SimpleGraph.edgeSet_mono hGH
    have hfiniteH : H.edgeSet.Finite := Set.toFinite _
    exact Set.ncard_le_ncard hEdges hfiniteH