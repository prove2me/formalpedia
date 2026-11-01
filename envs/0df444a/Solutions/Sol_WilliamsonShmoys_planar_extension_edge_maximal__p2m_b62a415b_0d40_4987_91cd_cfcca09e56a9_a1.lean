-- Prove2me | solution 1 for WilliamsonShmoys.planar_extension_edge_maximal__p2m_b62a415b_0d40_4987_91cd_cfcca09e56a9_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:16:33.675795+00:00
-- url     : https://prove2.me/submissions/e52c984a-f1ca-4455-be20-354ed7e88723

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ (H : SimpleGraph V) (hdec : DecidableRel H.Adj),
      G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      G.edgeFinset.card ≤ H.edgeFinset.card ∧
      ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H := by
  classical
  let S : Set (SimpleGraph V) :=
    {K | G ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K}
  have hS_nonempty : S.Nonempty := ⟨G, le_rfl, hG⟩
  have hS_finite : S.Finite := Set.toFinite S
  obtain ⟨H, hHmax⟩ := hS_finite.exists_maximal hS_nonempty
  have hHmem : G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H := hHmax.1
  letI : DecidableRel H.Adj := Classical.decRel _
  refine ⟨H, inferInstance, hHmem.1, hHmem.2, ?_, ?_⟩
  · exact Finset.card_le_card (SimpleGraph.edgeFinset_mono hHmem.1)
  · intro K hHK hKplanar
    have hKmem : K ∈ S := ⟨hHmem.1.trans hHK, hKplanar⟩
    exact le_antisymm (hHmax.2 hKmem hHK) hHK
