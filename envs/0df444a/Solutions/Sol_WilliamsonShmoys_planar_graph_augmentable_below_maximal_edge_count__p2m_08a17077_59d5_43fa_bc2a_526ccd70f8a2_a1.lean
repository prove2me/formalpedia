-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_augmentable_below_maximal_edge_count__p2m_08a17077_59d5_43fa_bc2a_526ccd70f8a2_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:56:06.444207+00:00
-- url     : https://prove2.me/submissions/b6018961-2146-4279-b86f-ec3e4570a603

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_c6dfb36f_1111_44f0_ab98_16407e8ce911_a1
import Theorems.Thm_WilliamsonShmoys_edge_count_of_maximal_planar_graph__p2m_c6dfb36f_1111_44f0_ab98_16407e8ce911_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hH : HasPlanarDrawingOn H)
    (hE : H.edgeSet.ncard < 3 * Fintype.card V - 6) :
    ∃ K : SimpleGraph V, H ≤ K ∧ K ≠ H ∧ HasPlanarDrawingOn K := by
  obtain ⟨K, hHK, hKdraw, hKmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_c6dfb36f_1111_44f0_ab98_16407e8ce911_a1
      H hH
  have hKcount :=
    WilliamsonShmoys.edge_count_of_maximal_planar_graph__p2m_c6dfb36f_1111_44f0_ab98_16407e8ce911_a1
      K hV hKdraw hKmax
  refine ⟨K, hHK, ?_, hKdraw⟩
  intro hKH
  rw [hKH] at hKcount
  omega