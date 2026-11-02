-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_supergraph_maximal__p2m_b6e1b838_6a07_4127_97a1_2301fa6a9ddd_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:16:10.725185+00:00
-- url     : https://prove2.me/submissions/ebd152dc-d1ce-42bc-88e5-2e13fb8b7a97

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_maximal_extension__p2m_6dfd0e85_ae5a_4e02_9c9b_5863f1785ef0_a1
import Theorems.Thm_WilliamsonShmoys_strict_edge_card_of_strict_subgraph__p2m_6dfd0e85_ae5a_4e02_9c9b_5863f1785ef0_a2
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V, M ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧
      ∀ K : SimpleGraph V, N ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = N := by
  classical
  obtain ⟨N, hMN, hN, hmax⟩ :=
    WilliamsonShmoys.finite_maximal_extension__p2m_6dfd0e85_ae5a_4e02_9c9b_5863f1785ef0_a1
      (R := fun G H : SimpleGraph V => G ≤ H)
      (μ := fun G => G.edgeFinset.card)
      (P := fun G => M ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G)
      (fun G => le_rfl)
      (fun G H K hGH hHK => hGH.trans hHK)
      (fun G H hGH hne =>
        WilliamsonShmoys.strict_edge_card_of_strict_subgraph__p2m_6dfd0e85_ae5a_4e02_9c9b_5863f1785ef0_a2
          hGH hne)
      M ⟨le_rfl, hM⟩
  refine ⟨N, hMN, hN.2, ?_⟩
  intro K hNK hK
  exact hmax K hNK ⟨hMN.trans hNK, hK⟩
