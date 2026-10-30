-- Prove2me | solution 1 for WilliamsonShmoys.sequence_of_bridge_extension__p2m_9960b19b_62d8_4924_9bd4_14f246de67e1_a3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:07:15.085011+00:00
-- url     : https://prove2.me/submissions/991dc709-48b4-4a66-90ac-b5550cada387
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WilliamsonShmoys_edge_enumeration__p2m_5afb1874_83c6_4429_86a3_ce5c27512c9e_a1
import Theorems.Thm_WilliamsonShmoys_sequence_from_edge_enumeration__p2m_5afb1874_83c6_4429_86a3_ce5c27512c9e_a1

set_option autoImplicit false

open SimpleGraph

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M H : SimpleGraph V)
    (hMH : M ≤ H)
    (hconn : H.Connected)
    (hbridge : ∀ u v : V, H.Adj u v → ¬ M.Adj u v →
      ¬ (H.deleteEdges {s(u, v)}).Reachable u v) :
    ∃ (n : Nat) (f : Fin (n + 1) → SimpleGraph V),
      f 0 = M ∧
      (∀ x y : V, (f (Fin.last n)).Reachable x y) ∧
      (∀ i : Fin n, ∃ x y : V,
        ¬ (f i.castSucc).Reachable x y ∧
        ∀ u v : V,
          (f i.succ).Adj u v ↔
            (f i.castSucc).Adj u v ∨
              ((u = x ∧ v = y) ∨ (u = y ∧ v = x))) := by
  obtain ⟨n, e, hcanon, hedge, hdistinct, hcover⟩ :=
    WilliamsonShmoys.edge_enumeration__p2m_5afb1874_83c6_4429_86a3_ce5c27512c9e_a1 M H hMH
  obtain ⟨f, hf0, hfinal, hsteps⟩ :=
    WilliamsonShmoys.sequence_from_edge_enumeration__p2m_5afb1874_83c6_4429_86a3_ce5c27512c9e_a1
      M H hMH hconn hbridge e hcanon hedge hdistinct hcover
  exact ⟨n, f, hf0, hfinal, hsteps⟩