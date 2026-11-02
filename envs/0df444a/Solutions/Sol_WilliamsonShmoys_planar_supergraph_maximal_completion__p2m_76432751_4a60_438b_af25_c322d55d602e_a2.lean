-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_maximal_completion__p2m_76432751_4a60_438b_af25_c322d55d602e_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:44:20.077466+00:00
-- url     : https://prove2.me/submissions/7fe8d966-5732-472d-ac5d-ae89368b6edc

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_maxEdge__p2m_0e267cb6_c5af_47f0_9958_0b72bfd3b3ee_a2
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 <= Fintype.card V) :
    ∃ H : SimpleGraph V, ∃ (dH : DecidableRel H.Adj),
      (letI : DecidableRel H.Adj := dH
       G.edgeFinset ⊆ H.edgeFinset ∧
       WilliamsonShmoys.HasPlanarDrawingOn H ∧
       ∀ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
         letI : DecidableRel K.Adj := dK
         WilliamsonShmoys.HasPlanarDrawingOn K →
         H.edgeFinset ⊆ K.edgeFinset →
         K.edgeFinset ⊆ H.edgeFinset) := by
  classical
  obtain ⟨H, dH, hGH, hH, hmax⟩ :=
    WilliamsonShmoys.exists_planar_supergraph_maxEdge__p2m_0e267cb6_c5af_47f0_9958_0b72bfd3b3ee_a2
      G hG
  refine ⟨H, dH, hGH, hH, ?_⟩
  intro K dK hK hHK
  letI : DecidableRel H.Adj := dH
  letI : DecidableRel K.Adj := dK
  have hcard := hmax K dK hK hHK
  have hedge : H.edgeFinset = K.edgeFinset :=
    Finset.eq_of_subset_of_card_le hHK hcard
  simpa [hedge]
