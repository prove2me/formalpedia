-- Prove2me | solution 1 for WilliamsonShmoys.bridge_augmented_graph_adj_iff__p2m_e1c10048_df1f_49a0_8080_5a203a611921_a3
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-02T22:36:30.464361+00:00
-- url     : https://prove2.me/submissions/87fda156-ad74-478a-b735-c6c12b742722

import Theorems.Thm_WilliamsonShmoys_bridge_augmented_graph_adj_iff__p2m_e1c10048_df1f_49a0_8080_5a203a611921_a4

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

open WilliamsonShmoys

theorem solution
    {V : Type} [LinearOrder V]
    (H : SimpleGraph V) (u v : V) (huv : u < v) :
    ∀ a b, a < b →
      ((H ⊔ SimpleGraph.fromRel (fun x y => x = u ∧ y = v)).Adj a b ↔
        H.Adj a b ∨ (a = u ∧ b = v)) :=
  WilliamsonShmoys.bridge_augmented_graph_adj_iff__p2m_e1c10048_df1f_49a0_8080_5a203a611921_a4 H u v huv