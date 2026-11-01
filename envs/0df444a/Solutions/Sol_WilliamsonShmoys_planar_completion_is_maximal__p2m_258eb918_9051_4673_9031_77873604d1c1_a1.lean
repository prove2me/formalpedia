-- Prove2me | solution 1 for WilliamsonShmoys.planar_completion_is_maximal__p2m_258eb918_9051_4673_9031_77873604d1c1_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:51:49.283103+00:00
-- url     : https://prove2.me/submissions/59cdb4b3-df2b-49d6-993a-d30e36f6339e

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_edge_maximizer__p2m_f914dab2_91be_415e_a370_d761f8bbdaba_a1
import Theorems.Thm_WilliamsonShmoys_strict_edgeSet_ncard_of_strict_extension__p2m_f914dab2_91be_415e_a370_d761f8bbdaba_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V, G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V,
        H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H := by
  classical
  obtain ⟨H, hGH, hH, hmax⟩ :=
    WilliamsonShmoys.planar_supergraph_edge_maximizer__p2m_f914dab2_91be_415e_a370_d761f8bbdaba_a1
      G hcard hG
  refine ⟨H, hGH, hH, ?_⟩
  intro K hHK hK
  by_contra hKH
  have hlt :=
    WilliamsonShmoys.strict_edgeSet_ncard_of_strict_extension__p2m_f914dab2_91be_415e_a370_d761f8bbdaba_a1
      H K hHK hKH
  have hle := hmax K hHK hK
  omega
