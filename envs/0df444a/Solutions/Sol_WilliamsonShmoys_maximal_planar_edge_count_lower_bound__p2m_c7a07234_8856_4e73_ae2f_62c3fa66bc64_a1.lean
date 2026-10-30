-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_c7a07234_8856_4e73_ae2f_62c3fa66bc64_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T21:32:54.904307+00:00
-- url     : https://prove2.me/submissions/6174f74d-8eac-4b21-9065-73837eb1bba1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_completion_edge_count__p2m_295c0ef8_5d8f_41a3_8c9f_ccd6cdcf9c48_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hCard : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V, N ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K →
      K.edgeSet.ncard ≤ N.edgeSet.ncard) :
    3 * Fintype.card V - 6 ≤ N.edgeSet.ncard := by
  obtain ⟨K, hNK, hK, hEdges⟩ :=
    WilliamsonShmoys.planar_completion_edge_count__p2m_295c0ef8_5d8f_41a3_8c9f_ccd6cdcf9c48_a2
      N hN hCard
  calc
    3 * Fintype.card V - 6 = K.edgeSet.ncard := hEdges.symm
    _ ≤ N.edgeSet.ncard := hmax K hNK hK