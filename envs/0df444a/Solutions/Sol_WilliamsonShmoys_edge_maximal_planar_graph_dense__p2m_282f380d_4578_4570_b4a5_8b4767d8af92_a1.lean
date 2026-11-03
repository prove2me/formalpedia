-- Prove2me | solution 1 for WilliamsonShmoys.edge_maximal_planar_graph_dense__p2m_282f380d_4578_4570_b4a5_8b4767d8af92_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:48:54.582892+00:00
-- url     : https://prove2.me/submissions/9d3ff7c4-405a-4e56-8c20-7ace7b20d2ac

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_9948da09_8892_4f55_9a10_a3a5f578a96b_a1
import Mathlib
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K) :
    3 * Fintype.card V - 6 ≤ K.edgeSet.ncard := by
  obtain ⟨L, hKL, hL, hLcount⟩ :=
    WilliamsonShmoys.planar_triangulation_extension__p2m_9948da09_8892_4f55_9a10_a3a5f578a96b_a1
      K hK hcard
  have hLK : L ≤ K := hmax L hKL hL
  have hEq : L = K := le_antisymm hLK hKL
  rw [← hEq]
  omega