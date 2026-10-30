-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_0319396f
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T01:40:45.098985+00:00
-- url     : https://prove2.me/submissions/23891121-e3d8-4165-8f4c-f7d3fb3d5b26

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_completion_with_maximal_edge_count_0319396f

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K)
    (hV : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨L, hKL, hL, hcount⟩ :=
    WilliamsonShmoys.exists_planar_completion_with_maximal_edge_count_0319396f K hK hV
  have hLK : L = K := hmax L hKL hL
  simpa [hLK] using hcount