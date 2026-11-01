-- Prove2me | solution 1 for WilliamsonShmoys_exists_inclusion_maximal_planar_supergraph__p2m_b5bac186_dc32_4d53_bbd2_ff87f7d5377f_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:05:42.058988+00:00
-- url     : https://prove2.me/submissions/8a36ecd5-ddd2-494d-8937-2c742e3c401b

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ (H : SimpleGraph V) (dH : DecidableRel H.Adj),
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      L.edgeFinset ⊆ H.edgeFinset ∧
      ∀ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
        WilliamsonShmoys.HasPlanarDrawingOn K →
        H.edgeFinset ⊆ K.edgeFinset →
        K.edgeFinset ⊆ H.edgeFinset := by
  classical
  let s : Set (SimpleGraph V) :=
    {G | WilliamsonShmoys.HasPlanarDrawingOn G ∧ L ≤ G}
  have hsFinite : s.Finite := Set.toFinite s
  have hsNonempty : s.Nonempty := ⟨L, hL, le_rfl⟩
  obtain ⟨H, hHmax⟩ := hsFinite.exists_maximal hsNonempty
  have hHmem : H ∈ s := hHmax.1
  have hLleH : L ≤ H := hHmem.2
  let dH : DecidableRel H.Adj := Classical.decRel _
  refine ⟨H, dH, hHmem.1,
    (SimpleGraph.edgeFinset_subset_edgeFinset).2 hLleH, ?_⟩
  intro K dK hK hHK
  have hLH : L.edgeFinset ⊆ H.edgeFinset :=
    (SimpleGraph.edgeFinset_subset_edgeFinset).2 hLleH
  have hLK : L.edgeFinset ⊆ K.edgeFinset := Finset.Subset.trans hLH hHK
  have hLleK : L ≤ K :=
    (SimpleGraph.edgeFinset_subset_edgeFinset).1 hLK
  have hKmem : K ∈ s := ⟨hK, hLleK⟩
  have hHleK : H ≤ K :=
    (SimpleGraph.edgeFinset_subset_edgeFinset).1 hHK
  have hKleH : K ≤ H := hHmax.2 hKmem hHleK
  exact (SimpleGraph.edgeFinset_subset_edgeFinset).2 hKleH