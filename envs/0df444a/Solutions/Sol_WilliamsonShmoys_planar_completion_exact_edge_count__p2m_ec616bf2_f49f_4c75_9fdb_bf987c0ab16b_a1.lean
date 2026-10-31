-- Prove2me | solution 1 for WilliamsonShmoys.planar_completion_exact_edge_count__p2m_ec616bf2_f49f_4c75_9fdb_bf987c0ab16b_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:56:26.663441+00:00
-- url     : https://prove2.me/submissions/75c531ac-a1c1-4313-a912-da3144503393

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_maximal_extension__p2m_e7b99952_d0a7_4658_9396_b1a5968fd530_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_e7b99952_d0a7_4658_9396_b1a5968fd530_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ N : SimpleGraph V,
      K.edgeSet ⊆ N.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      N.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨N, hKN, hN, hmax⟩ :=
    WilliamsonShmoys.planar_supergraph_maximal_extension__p2m_e7b99952_d0a7_4658_9396_b1a5968fd530_a1 K hK
  have hcount :=
    WilliamsonShmoys.maximal_planar_edge_count__p2m_e7b99952_d0a7_4658_9396_b1a5968fd530_a1 N hV hN hmax
  exact ⟨N, hKN, hN, hcount⟩