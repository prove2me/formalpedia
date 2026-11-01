-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_augmentation_below_bound__p2m_8532617a_0690_495a_a2cc_fdaf4080cf05_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:46:13.650066+00:00
-- url     : https://prove2.me/submissions/7f1e6df8-56af-40a2-a042-8f7325459c85

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_b501a266_2ceb_4b60_9d31_7e031b204a4c_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count__p2m_b501a266_2ceb_4b60_9d31_7e031b204a4c_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hcard : 3 ≤ Fintype.card V)
    (hsmall : T.edgeSet.ncard < 3 * Fintype.card V - 6) :
    ∃ U : SimpleGraph V,
      T.edgeSet ⊆ U.edgeSet ∧
      ∃ e, e ∈ U.edgeSet ∧ e ∉ T.edgeSet ∧
        WilliamsonShmoys.HasPlanarDrawingOn U := by
  classical
  obtain ⟨M, hTM, hM, hMax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_b501a266_2ceb_4b60_9d31_7e031b204a4c_a1
      T hT
  have hCount :=
    WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_b501a266_2ceb_4b60_9d31_7e031b204a4c_a1
      M hM hcard hMax
  have hnew : ¬ M.edgeSet ⊆ T.edgeSet := by
    intro hMT
    have heq : T.edgeSet = M.edgeSet := Set.Subset.antisymm hTM hMT
    rw [← heq] at hCount
    omega
  obtain ⟨e, heM, heT⟩ := Set.not_subset.mp hnew
  exact ⟨M, hTM, e, heM, heT, hM⟩
