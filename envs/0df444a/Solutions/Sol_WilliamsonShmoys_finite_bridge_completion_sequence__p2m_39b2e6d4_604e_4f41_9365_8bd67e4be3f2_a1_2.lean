-- Prove2me | solution 2 for WilliamsonShmoys.finite_bridge_completion_sequence__p2m_39b2e6d4_604e_4f41_9365_8bd67e4be3f2_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:17:43.999822+00:00
-- url     : https://prove2.me/submissions/616b5b18-b734-4e6a-b597-a737ffa35169
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WilliamsonShmoys_exists_minimal_connected_extension__p2m_9960b19b_62d8_4924_9bd4_14f246de67e1_a4
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
  classical
  rcases isEmpty_or_nonempty V with hV | hV
  · refine ⟨0, fun _ => M, ?_, ?_, ?_⟩
    · rfl
    · intro x
      exact isEmptyElim (hV.false x)
    · intro i
      exact Fin.elim0 i
  · obtain ⟨H, hMH, hconn, hbridge⟩ :=
      WilliamsonShmoys.exists_minimal_connected_extension__p2m_9960b19b_62d8_4924_9bd4_14f246de67e1_a4
        (V := V) M
    exact WilliamsonShmoys.sequence_of_bridge_extension__p2m_9960b19b_62d8_4924_9bd4_14f246de67e1_a3
      M H hMH hconn hbridge