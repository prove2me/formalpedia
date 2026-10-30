-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximum_of_bounded_nat_predicate__p2m_14e5a5b6_f5c8_41dc_9ffe_e2b4f22f7e7c_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:09:26.653836+00:00
-- url     : https://prove2.me/submissions/9ac9f79e-e5c8-46f5-ac5a-ed50d27aa1cd

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    (P : Nat → Prop) (B : Nat)
    (hbounded : ∀ n, P n → n ≤ B)
    (hnonempty : ∃ n, P n) :
    ∃ n, P n ∧ ∀ m, P m → m ≤ n := by
  revert hbounded hnonempty
  induction B with
  | zero =>
      intro hbounded hnonempty
      rcases hnonempty with ⟨n, hn⟩
      have hn0 : n = 0 := Nat.eq_zero_of_le_zero (hbounded n hn)
      subst n
      refine ⟨0, hn, ?_⟩
      intro m hm
      exact hbounded m hm
  | succ B ih =>
      intro hbounded hnonempty
      by_cases htop : P (B + 1)
      · refine ⟨B + 1, htop, ?_⟩
        intro m hm
        exact hbounded m hm
      · have hbounded' : ∀ n, P n → n ≤ B := by
          intro n hn
          have hle : n ≤ B + 1 := hbounded n hn
          by_contra hnot
          have heq : n = B + 1 := by omega
          subst n
          exact False.elim (htop hn)
        exact ih hbounded' hnonempty