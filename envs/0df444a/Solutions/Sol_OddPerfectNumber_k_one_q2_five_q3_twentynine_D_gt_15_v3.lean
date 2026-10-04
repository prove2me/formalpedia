-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentynine_D_gt_15_v3
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-09-22T14:31:27.107642+00:00
-- url     : https://prove2.me/submissions/24a1843a-9865-47c2-814f-4266cca5201b

import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

private theorem ratio_lower (q N n : Nat) (hn : N ≤ n) :
    (∑ i ∈ Finset.range (N + 1), q ^ i) * q ^ n ≤
      q ^ N * (∑ i ∈ Finset.range (n + 1), q ^ i) := by
  induction n, hn using Nat.le_induction with
  | base => exact le_of_eq (mul_comm _ _)
  | succ n hn ih =>
    rw [pow_succ, geom_sum_succ (x := q) (n := n + 1)]
    calc
      (∑ i ∈ Finset.range (N + 1), q ^ i) * (q ^ n * q) =
          q * ((∑ i ∈ Finset.range (N + 1), q ^ i) * q ^ n) := by ac_rfl
      _ ≤ q * (q ^ N * ∑ i ∈ Finset.range (n + 1), q ^ i) :=
        Nat.mul_le_mul_left q ih
      _ = q ^ N * (q * ∑ i ∈ Finset.range (n + 1), q ^ i) := by ac_rfl
      _ ≤ q ^ N * (q * (∑ i ∈ Finset.range (n + 1), q ^ i) + 1) :=
        Nat.mul_le_mul_left _ (Nat.le_add_right _ _)

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentynine_D_gt_15_v3 (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 29 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 29 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2) (hp : p.Prime)
    (hp_eq : p = 2 * D - 1) (hq4prime : q4.Prime) (hq4gt : 29 < q4)
    (hDq : D < q4) (ha : 8 ≤ a) (hb : 6 ≤ b) (hc : 4 ≤ c)
    (he : 1 ≤ e) : 15 < D := by
  have h3 := ratio_lower 3 6 (2*a) (by omega)
  have h5 := ratio_lower 5 4 (2*b) (by omega)
  have h29 := ratio_lower 29 1 (2*c) (by omega)
  change 1093 * 3 ^ (2*a) ≤ 729 * (∑ i ∈ Finset.range (2*a+1), 3 ^ i) at h3
  change 781 * 5 ^ (2*b) ≤ 625 * (∑ i ∈ Finset.range (2*b+1), 5 ^ i) at h5
  change 30 * 29 ^ (2*c) ≤ 29 * (∑ i ∈ Finset.range (2*c+1), 29 ^ i) at h29
  have hq : q4 ^ (2*e) ≤ ∑ i ∈ Finset.range (2*e+1), q4 ^ i := by
    simpa using ratio_lower q4 0 (2*e) (Nat.zero_le _)
  have hmul := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul h3 h5) h29) hq
  have hcross : 25608990 * m ^ 2 ≤ 13213125 * sigma := by
    rw [hfac, hsigma]
    convert hmul using 1 <;> ring
  have hmpos : 0 < m ^ 2 := by
    rw [hfac]
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.pow_pos (by decide))
      (Nat.pow_pos (by decide))) (Nat.pow_pos (by decide))) (Nat.pow_pos (by omega))
  have hineq : 25608990 * D * m ^ 2 ≤ 13213125 * p * m ^ 2 := by
    calc
      25608990 * D * m ^ 2 = D * (25608990 * m ^ 2) := by ring
      _ ≤ D * (13213125 * sigma) := Nat.mul_le_mul_left D hcross
      _ = 13213125 * (D * sigma) := by ring
      _ = 13213125 * p * m ^ 2 := by rw [hrel]; ring
  have hbound := le_of_mul_le_mul_right hineq hmpos
  rw [hp_eq] at hbound
  have hp2 := hp.two_le
  omega

end OddPerfectNumber

theorem solution (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 29 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 29 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2) (hp : p.Prime)
    (hp_eq : p = 2 * D - 1) (hq4prime : q4.Prime) (hq4gt : 29 < q4)
    (hDq : D < q4) (ha : 8 ≤ a) (hb : 6 ≤ b) (hc : 4 ≤ c)
    (he : 1 ≤ e) : 15 < D :=
  OddPerfectNumber.k_one_q2_five_q3_twentynine_D_gt_15_v3 m a b c e D p q4 sigma hfac hsigma hrel hp hp_eq
    hq4prime hq4gt hDq ha hb hc he

#print axioms solution
