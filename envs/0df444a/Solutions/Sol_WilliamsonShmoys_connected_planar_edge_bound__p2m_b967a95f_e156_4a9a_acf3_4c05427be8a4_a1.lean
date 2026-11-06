-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_bound__p2m_b967a95f_e156_4a9a_acf3_4c05427be8a4_a1
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T15:01:24.210204+00:00
-- url     : https://prove2.me/submissions/24f869b5-0e83-4cf5-9089-e048cb16adc6

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
set_option autoImplicit false
open WilliamsonShmoys
-- ID: e1740105-f704-4603-9962-5c549f8c453b | NAME: WilliamsonShmoys.connected_planar_edge_bound__p2m_b967a95f_e156_4a9a_acf3_4c05427be8a4_a2 | 未本地编译验证

theorem solution {U : Type} [Fintype U] [LinearOrder U]
    (hconnected : ∀ {W : Type} [Fintype W] [LinearOrder W]
      (N : SimpleGraph W) (dN : DecidableRel N.Adj),
      HasPlanarDrawingOn N → N.Connected → 3 ≤ Fintype.card W →
      N.edgeFinset.card ≤ 3 * Fintype.card W - 6)
    (N : SimpleGraph U) (dN : DecidableRel N.Adj)
    (hN : HasPlanarDrawingOn N) (hc : N.Connected) :
    (3 ≤ Fintype.card U → N.edgeFinset.card ≤ 3 * Fintype.card U - 6) ∧
    (Fintype.card U < 3 → N.edgeFinset.card ≤ Fintype.card U) := by
  constructor
  · intro h3
    exact hconnected N dN hN hc h3
  · intro hsmall
    have hle : N.edgeFinset.card ≤ (Fintype.card U).choose 2 := by
      exact SimpleGraph.card_edgeFinset_le_card_choose_two (G := N)
    have hchoose : (Fintype.card U).choose 2 ≤ Fintype.card U := by
      by_cases h0 : Fintype.card U = 0
      · rw [h0]; norm_num
      by_cases h1 : Fintype.card U = 1
      · rw [h1]; norm_num
      have h2 : Fintype.card U = 2 := by omega
      rw [h2]; norm_num
    exact le_trans hle hchoose
