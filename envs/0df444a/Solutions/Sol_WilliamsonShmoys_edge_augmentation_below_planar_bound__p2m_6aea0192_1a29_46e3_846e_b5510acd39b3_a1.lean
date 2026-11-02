-- Prove2me | solution 1 for WilliamsonShmoys.edge_augmentation_below_planar_bound__p2m_6aea0192_1a29_46e3_846e_b5510acd39b3_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:18:49.418173+00:00
-- url     : https://prove2.me/submissions/1b1b4615-0f5d-4964-b89f-86a83e1ee529
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_supergraph_exists__p2m_63ad9a14_da0c_4363_acd0_29ef03d610e6_a2
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count__p2m_63ad9a14_da0c_4363_acd0_29ef03d610e6_a2
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hn : 3 <= Fintype.card V)
    (hsmall : L.edgeFinset.card < 3 * Fintype.card V - 6) :
    ∃ (M : SimpleGraph V) (dM : DecidableRel M.Adj),
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      L.edgeFinset ⊆ M.edgeFinset ∧
      L.edgeFinset ≠ M.edgeFinset := by
  obtain ⟨M, dM, hM, hLM, hmax⟩ :=
    WilliamsonShmoys.maximal_drawable_supergraph_exists__p2m_63ad9a14_da0c_4363_acd0_29ef03d610e6_a2
      L hL
  have hEdges : L.edgeFinset ⊆ M.edgeFinset :=
    (SimpleGraph.edgeFinset_subset_edgeFinset).2 hLM
  refine ⟨M, dM, hM, hEdges, ?_⟩
  intro heq
  have hMcard :=
    WilliamsonShmoys.maximal_drawable_edge_count__p2m_63ad9a14_da0c_4363_acd0_29ef03d610e6_a2
      M dM hM hn hmax
  have hEq : L.edgeFinset.card = M.edgeFinset.card :=
    congrArg Finset.card heq
  omega