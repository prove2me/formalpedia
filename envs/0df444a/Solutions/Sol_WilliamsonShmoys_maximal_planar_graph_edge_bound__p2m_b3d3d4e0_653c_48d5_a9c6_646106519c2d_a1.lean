-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_bound__p2m_b3d3d4e0_653c_48d5_a9c6_646106519c2d_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T20:27:41.9758+00:00
-- url     : https://prove2.me/submissions/3453a0dd-f050-4f7e-9a08-e423abe28894

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion__p2m_ec3e03f0_5758_464a_8536_b42e2e8ffdc8_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hN : HasPlanarDrawingOn N)
    (hmax : ∀ P : SimpleGraph V, N ≤ P → HasPlanarDrawingOn P → P = N) :
    3 * Fintype.card V - 6 ≤ N.edgeSet.ncard := by
  obtain ⟨P, hNP, hP, hCount⟩ :=
    WilliamsonShmoys.planar_triangulation_completion__p2m_ec3e03f0_5758_464a_8536_b42e2e8ffdc8_a1 N hV hN
  have hPN : P = N := hmax P hNP hP
  rw [hPN] at hCount
  omega