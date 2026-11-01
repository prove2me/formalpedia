-- Prove2me | solution 1 for WilliamsonShmoys.inclusion_maximal_planar_drawing_is_connected__p2m_47afe67c_60e1_47f9_a634_1f5964e2e86e_a3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:20:56.459801+00:00
-- url     : https://prove2.me/submissions/7f0366dc-4897-436b-aa9c-e1742f0ac71b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_disconnected_planar_drawing_has_strict_planar_supergraph__p2m_c35528ef_9e7a_47ce_ad15_6f32623d8cca_a1
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N = M) :
    M.Connected := by
  by_contra hconn
  obtain ⟨N, hMN, hN, hneq⟩ :=
    WilliamsonShmoys.disconnected_planar_drawing_has_strict_planar_supergraph__p2m_c35528ef_9e7a_47ce_ad15_6f32623d8cca_a1 M hM hconn
  have hEq : N = M := hmax N hMN hN
  exact hneq hEq