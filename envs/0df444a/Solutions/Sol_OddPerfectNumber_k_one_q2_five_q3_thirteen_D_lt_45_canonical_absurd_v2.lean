-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_thirteen_D_lt_45_canonical_absurd_v2
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-20T03:21:55.13872+00:00
-- url     : https://prove2.me/submissions/debee27a-5d5c-44f6-8ad7-5d4a9476cd77

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_D_lt_45_candidates_v2
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_three_ge_two_sharp
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_five_ge_six
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_thirteen_ge_two
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_base_le47

/-
Abundance contradiction for the q2 = 5, q3 = 13, D < 45 canonical branch.

`candidates_v2` cuts the hypotheses down to the three arithmetic survivors
(D, p, q4) = (19, 37, 19), (31, 61, 31), (37, 73, 37).  In every one of them
q4 ≤ 47, so the four accepted geometric-ratio floors apply with the canonical
exponent floors a ≥ 2, b ≥ 8, c ≥ 2, e ≥ 1:

  9 * S(3,2a)    ≥ 13   * 3^(2a)
  3125 * S(5,2b) ≥ 3906 * 5^(2b)
  169 * S(13,2c) ≥ 183  * 13^(2c)
  47 * S(q4,2e)  ≥ 48   * q4^(2e)

Multiplying the four gives  223396875 * sigma ≥ 446033952 * m^2,
i.e. sigma / m^2 ≥ 446033952 / 223396875 = 1.99659... .
Feeding that into D * sigma = p * m^2 (and m^2 > 0) yields
446033952 * D ≤ 223396875 * p, which fails for each of the three survivors
because p / D is at most 73 / 37 = 1.97297... .
-/

theorem solution (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 13 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 13 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2)
    (hD : D < 45) (hp : p.Prime) (hp4 : p % 4 = 1)
    (hp_eq : p = 2 * D - 1) (hq4 : q4.Prime) (hq4gt : 13 < q4)
    (hq4dvd : q4 ∣ D)
    (ha : 2 ≤ a) (hb : 8 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e) : False := by
  -- the three arithmetic survivors of the D < 45 sieve
  have hcand :=
    OddPerfectNumber.k_one_q2_five_q3_thirteen_D_lt_45_candidates_v2 D p q4
      hD hp hp4 hp_eq hq4 hq4gt hq4dvd
  have hq4le : q4 ≤ 47 := by
    rcases hcand with ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> omega
  -- the four accepted geometric-ratio floors, at the canonical exponents
  have h3 : 13 * 3 ^ (2 * a) ≤ 9 * (∑ i ∈ Finset.range (2 * a + 1), 3 ^ i) :=
    OddPerfectNumber.geom_ratio_lower_three_ge_two_sharp (2 * a) (by omega)
  have h5 : 3906 * 5 ^ (2 * b) ≤ 3125 * (∑ i ∈ Finset.range (2 * b + 1), 5 ^ i) :=
    OddPerfectNumber.geom_ratio_lower_five_ge_six (2 * b) (by omega)
  have h13 : 183 * 13 ^ (2 * c) ≤ 169 * (∑ i ∈ Finset.range (2 * c + 1), 13 ^ i) :=
    OddPerfectNumber.geom_ratio_lower_thirteen_ge_two (2 * c) (by omega)
  have hqq : 48 * q4 ^ (2 * e) ≤ 47 * (∑ i ∈ Finset.range (2 * e + 1), q4 ^ i) :=
    OddPerfectNumber.geom_ratio_lower_base_le47 q4 (2 * e) hq4le (by omega)
  have hstep := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul h3 h5) h13) hqq
  have hpos : 0 < m ^ 2 := by
    rw [hfac]
    have p3 : 0 < (3 : Nat) ^ (2 * a) := by positivity
    have p5 : 0 < (5 : Nat) ^ (2 * b) := by positivity
    have p13 : 0 < (13 : Nat) ^ (2 * c) := by positivity
    have pq : 0 < q4 ^ (2 * e) := Nat.pow_pos hq4.pos
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos p3 p5) p13) pq
  -- the product of the four floors
  have key : 446033952 * m ^ 2 ≤ 223396875 * sigma := by
    calc 446033952 * m ^ 2
        = 13 * 3 ^ (2 * a) * (3906 * 5 ^ (2 * b)) * (183 * 13 ^ (2 * c)) *
            (48 * q4 ^ (2 * e)) := by rw [hfac]; ring
      _ ≤ 9 * (∑ i ∈ Finset.range (2 * a + 1), 3 ^ i) *
            (3125 * (∑ i ∈ Finset.range (2 * b + 1), 5 ^ i)) *
            (169 * (∑ i ∈ Finset.range (2 * c + 1), 13 ^ i)) *
            (47 * (∑ i ∈ Finset.range (2 * e + 1), q4 ^ i)) := hstep
      _ = 223396875 * sigma := by rw [hsigma]; ring
  -- transport through D * sigma = p * m ^ 2 and cancel m ^ 2
  have hmain : 446033952 * D ≤ 223396875 * p := by
    have h1 : 446033952 * D * m ^ 2 ≤ 223396875 * p * m ^ 2 := by
      calc 446033952 * D * m ^ 2 = D * (446033952 * m ^ 2) := by ring
        _ ≤ D * (223396875 * sigma) := Nat.mul_le_mul le_rfl key
        _ = 223396875 * (D * sigma) := by ring
        _ = 223396875 * (p * m ^ 2) := by rw [hrel]
        _ = 223396875 * p * m ^ 2 := by ring
    exact Nat.le_of_mul_le_mul_right h1 hpos
  rcases hcand with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ <;>
    rw [h1, h2] at hmain <;> norm_num at hmain