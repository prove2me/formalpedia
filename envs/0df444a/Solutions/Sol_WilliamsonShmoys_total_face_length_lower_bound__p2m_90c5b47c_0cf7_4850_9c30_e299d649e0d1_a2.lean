-- Prove2me | solution 1 for WilliamsonShmoys.total_face_length_lower_bound__p2m_90c5b47c_0cf7_4850_9c30_e299d649e0d1_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:56:52.317078+00:00
-- url     : https://prove2.me/submissions/cd39d128-4990-4654-bdc4-5def867f8c6a

import Mathlib
set_option autoImplicit false

theorem solution {V : Type} (k : Nat) (faces : Fin k -> List (Prod V V))
    (hlen : forall i, 3 <= (faces i).length) :
    3 * k <= (List.flatten (List.ofFn faces)).length := by
  induction k with
  | zero => simp
  | succ k ih =>
      let fs : Fin k -> List (Prod V V) := fun i => faces i.succ
      have hfs : forall i, 3 <= (fs i).length := by
        intro i
        exact hlen i.succ
      have hzero : 3 <= (faces 0).length := hlen 0
      have h := Nat.add_le_add hzero (ih fs hfs)
      simpa [fs, List.ofFn_succ, Nat.mul_succ, Nat.add_comm,
        Nat.add_left_comm, Nat.add_assoc] using h