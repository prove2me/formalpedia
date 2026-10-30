-- Prove2me | solution 1 for WilliamsonShmoys_finite_planar_supergraph_card_maximal__p2m_91ab9901_9648_4f4d_a2f0_8a8bd8921595_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:58:08.921542+00:00
-- url     : https://prove2.me/submissions/c840173b-0db9-43fa-b5f7-e4d3061309b7

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V, G.edgeSet ⊆ H.edgeSet ∧
      HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V, H.edgeSet ⊆ K.edgeSet →
        HasPlanarDrawingOn K → K.edgeSet.ncard ≤ H.edgeSet.ncard := by
  classical
  let S : Set (SimpleGraph V) :=
    {K | G.edgeSet ⊆ K.edgeSet ∧ HasPlanarDrawingOn K}
  have hS : S.Finite := Set.toFinite S
  obtain ⟨H, hH, hmax⟩ :=
    Set.exists_max_image S (fun K => K.edgeSet.ncard) hS
      ⟨G, Set.Subset.rfl, hG⟩
  refine ⟨H, hH.1, hH.2, ?_⟩
  intro K hHK hK
  exact hmax K ⟨hH.1.trans hHK, hK⟩