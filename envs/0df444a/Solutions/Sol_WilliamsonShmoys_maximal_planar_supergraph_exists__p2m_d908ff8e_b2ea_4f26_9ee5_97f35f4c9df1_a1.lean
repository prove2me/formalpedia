-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_supergraph_exists__p2m_d908ff8e_b2ea_4f26_9ee5_97f35f4c9df1_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:24:05.493109+00:00
-- url     : https://prove2.me/submissions/981c349a-a992-4bcd-9579-83246e423a65

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph_by_edge_count__p2m_bf560835_e420_42cf_80f6_9c119aabf70e_a1
import Theorems.Thm_WilliamsonShmoys_maximum_edge_count_implies_target_properties__p2m_bf560835_e420_42cf_80f6_9c119aabf70e_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
      (∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N = M) ∧
      (letI : DecidableRel L.Adj := Classical.decRel L.Adj
       L.edgeFinset.card ≤ M.edgeSet.ncard) := by
  obtain ⟨M, hLM, hM, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_drawable_supergraph_by_edge_count__p2m_bf560835_e420_42cf_80f6_9c119aabf70e_a1 L hL
  obtain ⟨hmaximal, hcount⟩ :=
    WilliamsonShmoys.maximum_edge_count_implies_target_properties__p2m_bf560835_e420_42cf_80f6_9c119aabf70e_a1 L M hLM hM hmax
  exact ⟨M, hLM, hM, hmaximal, hcount⟩