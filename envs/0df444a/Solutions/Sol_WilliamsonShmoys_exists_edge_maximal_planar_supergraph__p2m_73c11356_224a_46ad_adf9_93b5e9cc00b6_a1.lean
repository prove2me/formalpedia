-- Prove2me | solution 1 for WilliamsonShmoys.exists_edge_maximal_planar_supergraph__p2m_73c11356_224a_46ad_adf9_93b5e9cc00b6_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:03:02.130387+00:00
-- url     : https://prove2.me/submissions/4c55f77b-463d-412d-af56-90b3cac85e92

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_maximal_graph_property__p2m_ce5da3a5_6829_4f27_a8ae_e3e80a750393_a1
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V, L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N = M := by
  let Q : SimpleGraph V → Prop := fun G => L ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G
  have hQL : Q L := ⟨le_rfl, hL⟩
  obtain ⟨M, hLM, hQM, hmax⟩ :=
    WilliamsonShmoys.finite_maximal_graph_property__p2m_ce5da3a5_6829_4f27_a8ae_e3e80a750393_a1
      L Q hQL
  exact ⟨M, hLM, hQM.2, fun N hMN hN => hmax N hMN ⟨hLM.trans hMN, hN⟩⟩