-- Prove2me | solution 1 for WilliamsonShmoys.exists_edgeMaximal_planar_supergraph_same_vertex__p2m_3ee6bacb_2bd6_4aaa_b06f_7ea404afd915_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:10:21.418191+00:00
-- url     : https://prove2.me/submissions/10adf643-8706-48b8-961f-eece2ff6be16

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V, G ≤ H ∧ HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H := by
  classical
  let s : Set (SimpleGraph V) := {K | G ≤ K ∧ HasPlanarDrawingOn K}
  have hs : s.Nonempty := ⟨G, le_rfl, hG⟩
  have hsFinite : s.Finite := Set.toFinite s
  obtain ⟨H, hH, hmax⟩ := hsFinite.exists_maximal hs
  refine ⟨H, hH.1, hH.2, ?_⟩
  intro K hHK hK
  have hKmem : K ∈ s := ⟨hH.1.trans hHK, hK⟩
  exact le_antisymm (hmax hKmem hHK) hHK