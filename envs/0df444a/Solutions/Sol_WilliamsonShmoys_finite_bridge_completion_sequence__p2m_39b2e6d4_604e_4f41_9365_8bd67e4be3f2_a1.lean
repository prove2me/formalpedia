-- Prove2me | solution 1 for WilliamsonShmoys.finite_bridge_completion_sequence__p2m_39b2e6d4_604e_4f41_9365_8bd67e4be3f2_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:58:34.542754+00:00
-- url     : https://prove2.me/submissions/558b4e91-a86c-4d84-86bd-019da1079af2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WilliamsonShmoys_exists_minimal_connected_extension__p2m_9960b19b_62d8_4924_9bd4_14f246de67e1_a3
import Theorems.Thm_WilliamsonShmoys_sequence_of_bridge_extension__p2m_9960b19b_62d8_4924_9bd4_14f246de67e1_a3

set_option autoImplicit false

open SimpleGraph

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) :
    ∃ (n : Nat) (f : Fin (n + 1) → SimpleGraph V),
      f 0 = M ∧
      (∀ x y : V, (f (Fin.last n)).Reachable x y) ∧
      (∀ i : Fin n, ∃ x y : V,
        ¬ (f i.castSucc).Reachable x y ∧
        ∀ u v : V,
          (f i.succ).Adj u v ↔
            (f i.castSucc).Adj u v ∨
              ((u = x ∧ v = y) ∨ (u = y ∧ v = x))) := by
  obtain ⟨H, hMH, hconn, hbridge⟩ :=
    WilliamsonShmoys.exists_minimal_connected_extension__p2m_9960b19b_62d8_4924_9bd4_14f246de67e1_a3 M
  exact WilliamsonShmoys.sequence_of_bridge_extension__p2m_9960b19b_62d8_4924_9bd4_14f246de67e1_a3
    M H hMH hconn hbridge