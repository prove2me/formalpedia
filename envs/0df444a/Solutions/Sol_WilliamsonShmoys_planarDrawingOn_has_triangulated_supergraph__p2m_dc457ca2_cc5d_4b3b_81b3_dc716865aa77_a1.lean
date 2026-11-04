-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawingOn_has_triangulated_supergraph__p2m_dc457ca2_cc5d_4b3b_81b3_dc716865aa77_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:48:20.640751+00:00
-- url     : https://prove2.me/submissions/8f98a682-0d68-4fab-830e-fb99aa2fa1dd

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_has_edge_maximal_supergraph__p2m_a025b1a8_d903_4a44_81b6_ec9f7e2f3e4a_a1
import Theorems.Thm_WilliamsonShmoys_edge_maximal_planarDrawingOn_has_3n_sub_6_edges__p2m_a025b1a8_d903_4a44_81b6_ec9f7e2f3e4a_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : HasPlanarDrawingOn G)
    (hn : 3 ≤ Fintype.card V) :
    (letI : DecidableRel G.Adj := dG
     ∃ (H : SimpleGraph V) (dH : DecidableRel H.Adj),
       (letI : DecidableRel G.Adj := dG; letI : DecidableRel H.Adj := dH; G.edgeFinset ⊆ H.edgeFinset) ∧
       (letI : DecidableRel H.Adj := dH; H.edgeFinset.card = 3 * Fintype.card V - 6)) := by
  classical
  letI : DecidableRel G.Adj := dG
  obtain ⟨H, dH, hsub, hplanar, hmaximal⟩ :=
    WilliamsonShmoys.planarDrawingOn_has_edge_maximal_supergraph__p2m_a025b1a8_d903_4a44_81b6_ec9f7e2f3e4a_a1 G dG hG hn
  letI : DecidableRel H.Adj := dH
  have hcard :=
    WilliamsonShmoys.edge_maximal_planarDrawingOn_has_3n_sub_6_edges__p2m_a025b1a8_d903_4a44_81b6_ec9f7e2f3e4a_a1 H dH hplanar hn hmaximal
  exact ⟨H, dH, hsub, hcard⟩