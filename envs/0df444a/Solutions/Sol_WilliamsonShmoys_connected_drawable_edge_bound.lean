-- Prove2me | solution 1 for WilliamsonShmoys.connected_drawable_edge_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T23:02:49.425801+00:00
-- url     : https://prove2.me/submissions/51e6fd25-ebc2-40a4-a957-f556995f7d00
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_WilliamsonShmoys_PlanarFaceCountData__p2m_b6739023_548b_4b2e_a781_9b00cc5e2c81_a3
import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_faceCountData__p2m_b6739023_548b_4b2e_a781_9b00cc5e2c81_a3

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hConn : G.Connected)
    (hCard : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨q, length, hlength, hsum, heuler⟩ :=
    WilliamsonShmoys.planarDrawingOn_faceCountData__p2m_b6739023_548b_4b2e_a781_9b00cc5e2c81_a3
      G hDraw hConn hCard
  have hfaces : 3 * q ≤ ∑ f : Fin q, length f := by
    calc
      3 * q ≤ ∑ f : Fin q, 3 := by simp [Nat.mul_comm]
      _ ≤ ∑ f : Fin q, length f :=
        Finset.sum_le_sum fun f _ => hlength f
  rw [hsum] at hfaces
  omega