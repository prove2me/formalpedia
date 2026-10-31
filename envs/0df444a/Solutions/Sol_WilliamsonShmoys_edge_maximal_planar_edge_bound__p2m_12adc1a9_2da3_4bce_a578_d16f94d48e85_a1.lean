-- Prove2me | solution 1 for WilliamsonShmoys.edge_maximal_planar_edge_bound__p2m_12adc1a9_2da3_4bce_a578_d16f94d48e85_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:46:59.095251+00:00
-- url     : https://prove2.me/submissions/aa033c4e-ee59-4fa5-a7ea-0ebc8aeed326

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_completion_edge_count__p2m_84adf8d9_4f64_48f0_b013_da49e941db87_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K) :
    3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by
  obtain ⟨L, hKL, hLp, hEdges⟩ :=
    WilliamsonShmoys.planar_completion_edge_count__p2m_84adf8d9_4f64_48f0_b013_da49e941db87_a1
      K hK hCard
  have hEq : L = K := hMax L hKL hLp
  rw [← hEq]
  omega