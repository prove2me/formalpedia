-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_completion_edge_count_c0c3f643_3cd9_4990_9475_5983163d60d3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T06:15:14.755319+00:00
-- url     : https://prove2.me/submissions/a5b89397-588d-48d5-a4f6-f1dd9a53ae69

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_maximal_completion_b24ee22a_ee0a_4874_a748_da2528ed7758
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_b24ee22a_ee0a_4874_a748_da2528ed7758

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      3 * Fintype.card V = K.edgeSet.ncard + 6 := by
  obtain ⟨K, hHK, hK, hmax⟩ :=
    WilliamsonShmoys.planar_maximal_completion_b24ee22a_ee0a_4874_a748_da2528ed7758 H hH
  exact ⟨K, hHK, hK,
    WilliamsonShmoys.maximal_planar_edge_count_b24ee22a_ee0a_4874_a748_da2528ed7758 K hK hmax hCard⟩