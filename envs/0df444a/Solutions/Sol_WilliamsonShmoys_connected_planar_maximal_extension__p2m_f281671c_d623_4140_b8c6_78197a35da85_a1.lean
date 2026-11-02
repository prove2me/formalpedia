-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_maximal_extension__p2m_f281671c_d623_4140_b8c6_78197a35da85_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:17:05.718197+00:00
-- url     : https://prove2.me/submissions/eba24fb4-d9c3-4f3f-9653-dfab5ed71de7

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : HasPlanarDrawingOn G) (hconn : G.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ (H : SimpleGraph V) (dH : DecidableRel H.Adj),
      HasPlanarDrawingOn H ∧ G ≤ H ∧
      (letI : DecidableRel G.Adj := dG
       letI : DecidableRel H.Adj := dH
       G.edgeFinset.card ≤ H.edgeFinset.card) ∧
      (∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H) := by
  classical
  let S : Finset (SimpleGraph V) :=
    Finset.univ.filter (fun K => G ≤ K ∧ HasPlanarDrawingOn K)
  have hGmem : G ∈ S := by
    simp [S, hG]
  obtain ⟨H, hHmax⟩ := S.exists_maximal ⟨G, hGmem⟩
  have hHprops : G ≤ H ∧ HasPlanarDrawingOn H :=
    (Finset.mem_filter.mp hHmax.1).2
  refine ⟨H, inferInstance, hHprops.2, hHprops.1, ?_, ?_⟩
  · letI : DecidableRel G.Adj := dG
    letI : DecidableRel H.Adj := inferInstance
    exact Finset.card_le_card (SimpleGraph.edgeFinset_mono hHprops.1)
  · intro K hHK hK
    have hKH : K ≤ H := by
      apply hHmax.2
      · apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ K, ⟨hHprops.1.trans hHK, hK⟩⟩
      · exact hHK
    exact le_antisymm hKH hHK