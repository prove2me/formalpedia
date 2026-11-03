-- Prove2me | solution 1 for WilliamsonShmoys.planar_maximal_completion__p2m_8b510604_ecbe_41a0_8ffc_c43a355d8485_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:10:33.700702+00:00
-- url     : https://prove2.me/submissions/953ea005-d519-4c42-8385-d6c17fd94e68

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_connected_supergraph__p2m_81eecf30_e96c_499d_b4eb_13964c396f7c_a2
import Theorems.Thm_WilliamsonShmoys_connected_planar_maximal_extension__p2m_81eecf30_e96c_499d_b4eb_13964c396f7c_a2
import Theorems.Thm_WilliamsonShmoys_edge_card_mono__p2m_81eecf30_e96c_499d_b4eb_13964c396f7c_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hcard : 3 <= Fintype.card V) :
    letI : DecidableRel G.Adj := Classical.decRel _
    ∃ H : SimpleGraph V,
      (letI : DecidableRel H.Adj := Classical.decRel _;
       G ≤ H ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
       G.edgeFinset.card ≤ H.edgeSet.ncard ∧
       ∀ K : SimpleGraph V,
         (letI : DecidableRel K.Adj := Classical.decRel _;
          H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H)) := by
  letI : DecidableRel G.Adj := Classical.decRel _
  obtain ⟨C, hGC, hCconn, hCplanar⟩ :=
    WilliamsonShmoys.planar_connected_supergraph__p2m_81eecf30_e96c_499d_b4eb_13964c396f7c_a2
      G hG hcard
  obtain ⟨H, hCH, hHconn, hHplanar, hHmax⟩ :=
    WilliamsonShmoys.connected_planar_maximal_extension__p2m_81eecf30_e96c_499d_b4eb_13964c396f7c_a2
      C hCplanar hCconn
  refine ⟨H, ?_, hHconn, hHplanar, ?_, ?_⟩
  · exact le_trans hGC hCH
  · exact WilliamsonShmoys.edge_card_mono__p2m_81eecf30_e96c_499d_b4eb_13964c396f7c_a2
      G H (le_trans hGC hCH)
  · intro K
    letI : DecidableRel K.Adj := Classical.decRel _
    intro hHK hKplanar
    exact hHmax K hHK hKplanar