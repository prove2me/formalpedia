-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_maximal__p2m_8e688b5a_4cd6_4a71_af1c_8dd5b2ac94c3_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:57:51.934601+00:00
-- url     : https://prove2.me/submissions/95536339-1fea-4ec5-872f-4beff02a36c8

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_max_card__p2m_0b3013ac_25d6_4dd0_b6f8_fc82fd3d8fbf_a1
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_max_card_implies_maximal__p2m_0b3013ac_25d6_4dd0_b6f8_fc82fd3d8fbf_a1
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hn : 3 ≤ Fintype.card V) :
    ∃ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      G.edgeFinset ⊆ K.edgeFinset ∧
      (∀ (L : SimpleGraph V) (dL : DecidableRel L.Adj),
        WilliamsonShmoys.HasPlanarDrawingOn L →
        K.edgeFinset ⊆ L.edgeFinset → K.edgeFinset = L.edgeFinset) := by
  obtain ⟨K, dK, hK, hsub, hmax⟩ :=
    WilliamsonShmoys.planar_supergraph_max_card__p2m_0b3013ac_25d6_4dd0_b6f8_fc82fd3d8fbf_a1
      G dG hG
  exact ⟨K, dK, hK, hsub,
    WilliamsonShmoys.planar_supergraph_max_card_implies_maximal__p2m_0b3013ac_25d6_4dd0_b6f8_fc82fd3d8fbf_a1
      G dG K dK hK hsub hmax⟩