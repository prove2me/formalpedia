-- Prove2me | solution 1 for OddPerfectNumber.k_one_sigma_diophantine
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T06:10:43.861157+00:00
-- url     : https://prove2.me/submissions/ab07f479-1eb0-45f2-a3c6-55c4129aa669
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_diophantine_m_eq_one
import Theorems.Thm_OddPerfectNumber_k_one_diophantine_m_ge_two

open OddPerfectNumber

theorem solution (p m : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hpm : ¬ p ∣ m) (hm_odd : Odd m)
    (heq : (1 + p) * (∑ d ∈ (m ^ 2).divisors, d) = 2 * (p * m ^ 2)) : False := by
  by_cases hm1 : m = 1
  · subst hm1
    exact k_one_diophantine_m_eq_one p 1 hp hp4 hpm hm_odd rfl heq
  -- NB: remote `omega` cannot use hypothesis-form parity (row 332 CE on the
  -- sibling split), so destructure `Odd m` to a linear witness first.
  -- NB: `obtain` consumes the source hypothesis, so rebuild `Odd m`
  -- from the witness for the child application (row 337 CE).
  · obtain ⟨k, hk⟩ := hm_odd
    have hm2 : 2 ≤ m := by omega
    exact k_one_diophantine_m_ge_two p m hp hp4 hpm ⟨k, hk⟩ hm2 heq
