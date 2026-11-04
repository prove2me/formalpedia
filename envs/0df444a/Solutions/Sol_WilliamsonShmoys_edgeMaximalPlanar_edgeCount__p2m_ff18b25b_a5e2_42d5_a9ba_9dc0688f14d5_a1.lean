-- Prove2me | solution 1 for WilliamsonShmoys.edgeMaximalPlanar_edgeCount__p2m_ff18b25b_a5e2_42d5_a9ba_9dc0688f14d5_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:44:07.11521+00:00
-- url     : https://prove2.me/submissions/82531750-dcbd-425f-b19f-62eabcb3ae9a

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_edgeMaximalPlanar_connected__p2m_4c527512_1622_4d01_a868_d6bc284410d2_a1
import Theorems.Thm_WilliamsonShmoys_planar_edgeCount_upper__p2m_4c527512_1622_4d01_a868_d6bc284410d2_a1
import Theorems.Thm_WilliamsonShmoys_edgeMaximalPlanar_edgeCount_lower__p2m_4c527512_1622_4d01_a868_d6bc284410d2_a1
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : HasPlanarDrawingOn K)
    (hmax : ∀ H : SimpleGraph V, K ≤ H → HasPlanarDrawingOn H → H = K)
    (hn : 3 ≤ Fintype.card V) :
    ∀ [DecidableRel K.Adj], K.edgeFinset.card = 3 * Fintype.card V - 6 := by
  intro _
  have hconn := WilliamsonShmoys.edgeMaximalPlanar_connected__p2m_4c527512_1622_4d01_a868_d6bc284410d2_a1 K hK hmax hn
  have hupper := WilliamsonShmoys.planar_edgeCount_upper__p2m_4c527512_1622_4d01_a868_d6bc284410d2_a1 K hK hn
  have hlower := WilliamsonShmoys.edgeMaximalPlanar_edgeCount_lower__p2m_4c527512_1622_4d01_a868_d6bc284410d2_a1 K hK hmax hconn hn
  exact Nat.le_antisymm hupper hlower