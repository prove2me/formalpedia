-- Prove2me | solution 1 for OddPerfectNumber.Kernel.five_two_prime_first_equation_m_formula_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-05T17:44:44.788044+00:00
-- url     : https://prove2.me/submissions/702a1754-bd17-43dc-a2a1-f1d60a88c971

-- Proof for the PENDING publication v2 (he : p + 1 = 6 * u ^ 2).
-- Adapts solutionA.lean: hhalf0 : 2 * X = 6 * u ^ 2 where X = (p+1)/2.
-- hhalf : X = 3 * u ^ 2 by omega (linear in atoms X, u^2; no div reasoning needed).
-- Positivity side-goals use explicit `show (0:Nat) < 2` so no metavar is left for
-- the tactic block (7336 lesson: bare `by norm_num`/`by omega` as the first arg of
-- Nat.mul_left_cancel leaves `0 < ?m` unsolved).
import Mathlib

theorem solution (p m d1 q r u a b : Nat)
    (hp : p.Prime) (hp2 : p != 2)
    (he : p + 1 = 6 * u ^ 2)
    (hc : p ^ 2 + p + 1 = q * a ^ 2)
    (hd : p ^ 2 - p + 1 = 3 * r * b ^ 2)
    (h1 : 2 * m ^ 2 = (2 * (p ^ 2 + p + 1) * ((p + 1) / 2 * (p ^ 2 - p + 1))) *
      (d1 ^ 2 * (q * r))) :
    m = 3 * u * a * b * d1 * q * r := by
  have hp2u : p ≠ 2 := by simpa using hp2
  obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2u
  have heven : Even (p + 1) := ⟨k + 1, by rw [hk]; ring⟩
  have hmul : 2 * ((p + 1) / 2) = p + 1 := Nat.two_mul_div_two_of_even heven
  have hhalf0 : 2 * ((p + 1) / 2) = 6 * u ^ 2 := hmul.trans he
  have hhalf : (p + 1) / 2 = 3 * u ^ 2 := by omega
  have hprod : (2 * (p ^ 2 + p + 1) * ((p + 1) / 2 * (p ^ 2 - p + 1))) *
      (d1 ^ 2 * (q * r)) = 2 * (3 * u * a * b * d1 * q * r) ^ 2 := by
    rw [hc, hhalf, hd]
    ring
  have hsub : 2 * m ^ 2 = 2 * (3 * u * a * b * d1 * q * r) ^ 2 := h1.trans hprod
  have hsq : m ^ 2 = (3 * u * a * b * d1 * q * r) ^ 2 :=
    Nat.mul_left_cancel (show (0 : Nat) < 2 by norm_num) hsub
  calc m = Nat.sqrt (m ^ 2) := (Nat.sqrt_eq' m).symm
    _ = Nat.sqrt ((3 * u * a * b * d1 * q * r) ^ 2) := by rw [hsq]
    _ = 3 * u * a * b * d1 * q * r := Nat.sqrt_eq' _
