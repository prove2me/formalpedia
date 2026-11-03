-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_euler_bound__p2m_fa5d736f_5e40_4868_bcf6_007f98212d2a_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:43:03.448742+00:00
-- url     : https://prove2.me/submissions/f595471a-a1c1-4a2a-9875-f9fa6016de8e

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_8c5f7fcd_4410_4b31_b397_bfdf744b7888_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_euler_count__p2m_8c5f7fcd_4410_4b31_b397_bfdf744b7888_a2
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hconn : H.Connected)
    (hcard : 3 <= Fintype.card V) :
    letI : DecidableRel H.Adj := Classical.decRel H.Adj
    H.edgeFinset.card + 6 <= 3 * Fintype.card V := by
  classical
  have hext :=
    WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_8c5f7fcd_4410_4b31_b397_bfdf744b7888_a2 H hH
  let K : SimpleGraph V := Classical.choose hext
  have hspec := Classical.choose_spec hext
  have hHK : H <= K := hspec.1
  have hKplanar : WilliamsonShmoys.HasPlanarDrawingOn K := hspec.2.1
  have hKmax : forall K' : SimpleGraph V, K <= K' -> WilliamsonShmoys.HasPlanarDrawingOn K' -> K' = K := hspec.2.2
  have hKcount :=
    WilliamsonShmoys.maximal_planar_euler_count__p2m_8c5f7fcd_4410_4b31_b397_bfdf744b7888_a2
      K hKplanar hKmax hcard
  have hedge : H.edgeFinset.card <= K.edgeFinset.card :=
    Finset.card_le_card (SimpleGraph.edgeFinset_mono hHK)
  calc
    H.edgeFinset.card + 6 <= K.edgeFinset.card + 6 := Nat.add_le_add_right hedge 6
    _ = 3 * Fintype.card V := hKcount