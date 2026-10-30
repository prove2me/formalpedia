-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_edge_lower_bound_for_exact_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T05:57:40.848874+00:00
-- url     : https://prove2.me/submissions/cf7b312e-439e-4256-b62c-ab7c7172bc45

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_completion_edge_count_c0c3f643_3cd9_4990_9475_5983163d60d3

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hMax : ∀ K : SimpleGraph V,
      H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ H.edgeSet.ncard + 6 := by
  obtain ⟨K, hSub, hK, hCount⟩ :=
    WilliamsonShmoys.maximal_planar_completion_edge_count_c0c3f643_3cd9_4990_9475_5983163d60d3
      H hH hCard
  have hEq : K = H := hMax K hSub hK
  rw [hEq] at hCount
  exact le_of_eq hCount