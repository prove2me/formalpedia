-- Prove2me | solution 1 for ResourceScheduling.Graph.source_budget
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T14:28:09.292061+00:00
-- url     : https://prove2.me/submissions/7c9ec2ae-73b4-419e-9859-ebab0ac79aee

import Definitions.Def_CookPvsNP_defs
import Theorems.Thm_CookPvsNP_polynomial_absorb

set_option autoImplicit false

theorem solution (A d : ℕ) (hd : 2 ≤ d) : ∃ k, ∀ L c o : ℕ,
    c ≤ A * (100 * (L + 1)^2 + 1)^d → o ≤ 5 * L^2 + 8 → c + 3 * o + 2 ≤ L^k + k := by
  obtain ⟨k,hk⟩ := CookPvsNP.polynomial_absorb (A * 101 ^ d + 15) (2 * d) 26
  refine ⟨k, ?_⟩
  intro L c o hc ho
  apply le_trans _ (hk L)
  have hpos : 1 ≤ (L + 1)^2 := one_le_pow₀ (by omega)
  have hbase : 100 * (L + 1)^2 + 1 ≤ 101 * (L + 1)^2 := by nlinarith only [hpos]
  have hcost : c ≤ (A * 101 ^ d) * (L + 1)^(2*d) := by
    calc
      _ ≤ A * (100 * (L + 1)^2 + 1)^d := hc
      _ ≤ A * (101 * (L + 1)^2)^d := Nat.mul_le_mul_left A (Nat.pow_le_pow_left hbase d)
      _ = _ := by rw [mul_pow, ← pow_mul]; ring
  have hpow : L^2 ≤ (L + 1)^(2*d) :=
    (Nat.pow_le_pow_left (Nat.le_succ _) 2).trans
      (Nat.pow_le_pow_right (by omega) (by omega))
  nlinarith only [hcost, hpow, ho]

#print axioms solution
