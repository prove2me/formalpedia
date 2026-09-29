-- Prove2me | solution 1 for Rudin.Partition.point_mem
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-14T00:03:31.703595+00:00
-- url     : https://prove2.me/submissions/9fd99f6b-fffb-4f95-bfb6-3abb957202fc

import Mathlib
import Definitions.Def_Rudin_ch06_stieltjes

namespace Rudin

private lemma Partition.x_mono_aux {a b : ℝ} (P : Partition a b) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ P.n) : P.x i ≤ P.x j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | @succ j hij ih =>
      exact ih (Nat.le_trans (Nat.le_succ j) hj) |>.trans
        (P.mono j (Nat.lt_of_succ_le hj))

end Rudin

theorem solution {a b : ℝ} (P : Rudin.Partition a b) {i : ℕ}
    (hi : i ≤ P.n) : P.x i ∈ Set.Icc a b := by
  constructor
  · calc
      a = P.x 0 := P.first.symm
      _ ≤ P.x i := Rudin.Partition.x_mono_aux P (Nat.zero_le i) hi
  · calc
      P.x i ≤ P.x P.n := Rudin.Partition.x_mono_aux P hi le_rfl
      _ = b := P.last
