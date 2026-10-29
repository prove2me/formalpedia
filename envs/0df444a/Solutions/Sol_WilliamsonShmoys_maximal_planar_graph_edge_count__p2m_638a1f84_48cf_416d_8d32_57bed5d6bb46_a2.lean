-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_638a1f84_48cf_416d_8d32_57bed5d6bb46_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T18:47:55.121994+00:00
-- url     : https://prove2.me/submissions/45d03a65-e248-4402-a89c-6c10bb2afa1c

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion__p2m_0d3ba6cc_be4a_436c_b614_289a3ecc8076_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hmax : ∀ H : SimpleGraph V, K ≤ H →
      WilliamsonShmoys.HasPlanarDrawingOn H → H = K) :
    3 * Fintype.card V - 6 = K.edgeSet.ncard := by
  obtain ⟨H, hKH, hH, hcount⟩ :=
    WilliamsonShmoys.planar_triangulation_completion__p2m_0d3ba6cc_be4a_436c_b614_289a3ecc8076_a1
      K hK hCard
  have hEq : H = K := hmax H hKH hH
  rw [hEq] at hcount
  omega