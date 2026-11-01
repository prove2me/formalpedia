-- Prove2me | solution 1 for WilliamsonShmoys.finite_simple_graph_type__p2m_4d05bb9d_42a1_4f6c_b6b4_be7b1a8f6d1e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:41:47.540192+00:00
-- url     : https://prove2.me/submissions/74ea3a61-2be4-4fdd-a81c-533616b7d6e7

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] : Finite (SimpleGraph V) := by
  classical
  let adjacencyTable : SimpleGraph V → (V × V → Bool) :=
    fun G p => decide (G.Adj p.1 p.2)
  apply Finite.of_injective adjacencyTable
  intro G H h
  ext u v
  have hEq := congrFun h (u, v)
  change decide (G.Adj u v) = decide (H.Adj u v) at hEq
  by_cases hG : G.Adj u v <;> by_cases hH : H.Adj u v <;>
    simp [hG, hH] at hEq ⊢