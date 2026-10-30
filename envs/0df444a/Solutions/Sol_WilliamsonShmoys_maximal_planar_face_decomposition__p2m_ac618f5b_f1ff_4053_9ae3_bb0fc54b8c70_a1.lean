-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_face_decomposition__p2m_ac618f5b_f1ff_4053_9ae3_bb0fc54b8c70_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:32:47.053508+00:00
-- url     : https://prove2.me/submissions/7c0bd37b-ba20-438b-a718-67058b22ce22
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_upper_bound__p2m_ea40f167_79e5_4439_8a7d_ae09e117fb58_a3
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_ea40f167_79e5_4439_8a7d_ae09e117fb58_a3

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = L.edgeSet.ncard + 2 ∧
      3 * f = 2 * L.edgeSet.ncard := by
  let n := Fintype.card V
  let m := L.edgeSet.ncard
  have hUpper :=
    WilliamsonShmoys.maximal_planar_edge_upper_bound__p2m_ea40f167_79e5_4439_8a7d_ae09e117fb58_a3
      L hL hCard
  have hLower :=
    WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_ea40f167_79e5_4439_8a7d_ae09e117fb58_a3
      L hL hMax hCard
  have hEq : m + 6 = 3 * n := by omega
  refine ⟨2 * n - 4, ?_, ?_⟩ <;> dsimp [n, m] at * <;> omega