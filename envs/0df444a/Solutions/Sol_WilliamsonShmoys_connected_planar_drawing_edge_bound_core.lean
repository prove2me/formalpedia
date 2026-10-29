-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_drawing_edge_bound_core
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T02:10:38.744377+00:00
-- url     : https://prove2.me/submissions/8ca644e0-df4e-40e0-9c10-6fe1992837d6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_PlanarEulerData__p2m_d55c87f4_5c3d_477a_90f7_18a99497d822_a5
import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_data__p2m_d55c87f4_5c3d_477a_90f7_18a99497d822_a5
set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    (hConn : G.Connected) (hCard : 3 <= Fintype.card V) :
    G.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  rcases WilliamsonShmoys.planar_drawing_euler_data__p2m_d55c87f4_5c3d_477a_90f7_18a99497d822_a5
      G hG hConn hCard with ⟨D⟩
  have hfaces : 3 * D.faces__p2m_d55c87f4_5c3d_477a_90f7_18a99497d822_a5.card <=
      2 * G.edgeSet.ncard := by
    calc
      3 * D.faces__p2m_d55c87f4_5c3d_477a_90f7_18a99497d822_a5.card =
          ∑ f ∈ D.faces__p2m_d55c87f4_5c3d_477a_90f7_18a99497d822_a5, (3 : Nat) := by simp [Nat.mul_comm]
      _ <= ∑ f ∈ D.faces__p2m_d55c87f4_5c3d_477a_90f7_18a99497d822_a5,
          D.boundaryLength__p2m_d55c87f4_5c3d_477a_90f7_18a99497d822_a5 f := by
        apply Finset.sum_le_sum
        intro f hf
        exact D.boundaryLength_ge_three__p2m_d55c87f4_5c3d_477a_90f7_18a99497d822_a5 f hf
      _ = 2 * G.edgeSet.ncard := D.boundaryLength_sum__p2m_d55c87f4_5c3d_477a_90f7_18a99497d822_a5
  have heuler := D.euler__p2m_d55c87f4_5c3d_477a_90f7_18a99497d822_a5
  omega