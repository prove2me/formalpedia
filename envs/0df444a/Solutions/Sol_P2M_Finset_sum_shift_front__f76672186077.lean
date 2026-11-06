-- Prove2me | solution 1 for P2M_Finset_sum_shift_front__f76672186077
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:12:51.495056+00:00
-- url     : https://prove2.me/submissions/e7a74b61-d79b-48fb-bbad-28e8d9fc094a

import Definitions.Def_PrimeNumberTheoremAnd_Wiener

open BigOperators

theorem solution {E : Type*} [Ring E] {u : ℕ → E} :
    shift (cumsum u) = (fun _ => u 0) + cumsum (shift u) := by
  ext n
  simp_rw [shift, Pi.add_apply, add_comm n, cumsum, _root_.Finset.sum_range_add,
    _root_.Finset.sum_range_one, add_comm 1]
  rfl
