-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentythree_D_lt_111_abundance_cut_half_floors_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-17T13:27:38.940813+00:00
-- url     : https://prove2.me/submissions/596f4f54-5061-4bb0-8a7b-877041a842ec

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_D_lt_111_support_cases_v5
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_three_ge_eight
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_five_ge_six_sharp
import Theorems.Thm_OddPerfectNumber_geom_mul_sub_one
import Theorems.Thm_OddPerfectNumber_geom_sum_last_term_le

-- EXPONENT CONVENTION: a,b,c,e are HALF exponents; full floors are 8,6,4,2.
-- Weaker-interface replacement candidate; requires its own authoritative target.
-- Still a reduced cut: D < q4 and the half-exponent floors remain explicit.
theorem solution (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 23 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 23 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2) (hDlt : D < 111) (hDodd : Odd D)
    (hp : p.Prime) (hp_eq : p = 2 * D - 1) (hq4prime : q4.Prime)
    (hq4gt : 23 < q4) (hDq : D < q4)
    (hDsupport : ∀ r, r.Prime → r ∣ D →
      r = 3 ∨ r = 5 ∨ r = 23 ∨ r = q4)
    (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e) :
    D = 27 ∨ D = 45 ∨ D = 69 ∨ D = 75 := by
  have hcases := OddPerfectNumber.k_one_q2_five_q3_twentythree_D_lt_111_support_cases_v5
    D p q4 hDlt hDodd hp hp_eq hq4gt hDq hDsupport
  let S3 : Nat := ∑ i ∈ Finset.range (2*a + 1), 3 ^ i
  let S5 : Nat := ∑ i ∈ Finset.range (2*b + 1), 5 ^ i
  let S23 : Nat := ∑ i ∈ Finset.range (2*c + 1), 23 ^ i
  let Sq : Nat := ∑ i ∈ Finset.range (2*e + 1), q4 ^ i
  have h3 := OddPerfectNumber.geom_ratio_lower_three_ge_eight (2*a) (by omega)
  have h5 := OddPerfectNumber.geom_ratio_lower_five_ge_six_sharp (2*b) (by omega)
  have hgeom := OddPerfectNumber.geom_mul_sub_one 23 (2*c + 1) (by norm_num)
  rw [pow_succ] at hgeom
  have hpow23 : 23 ^ 4 ≤ 23 ^ (2*c) :=
    Nat.pow_le_pow_right (by norm_num : 0 < 23) (by omega)
  have h23 : 292561 * 23 ^ (2*c) ≤ 279841 * S23 := by
    dsimp [S23]
    omega
  have hq := OddPerfectNumber.geom_sum_last_term_le q4 (2*e)
  have hmul := Nat.mul_le_mul (Nat.mul_le_mul h3 h5) (Nat.mul_le_mul h23 hq)
  have hcross : 56231561496331 * m ^ 2 ≤ 28688075015625 * sigma := by
    calc
      56231561496331 * m ^ 2 =
          (9841 * 3^(2*a)) * (19531 * 5^(2*b)) *
            ((292561 * 23^(2*c)) * q4^(2*e)) := by rw [hfac]; ring
      _ ≤ (6561 * S3) * (15625 * S5) * ((279841 * S23) * Sq) := by
        simpa only [S3, S5, S23, Sq] using hmul
      _ = 28688075015625 * sigma := by rw [hsigma]; dsimp [S3, S5, S23, Sq]; ring
  have hmpos : 0 < m ^ 2 := by rw [hfac]; positivity
  have hineq : (56231561496331 * D) * m ^ 2 ≤
      (28688075015625 * p) * m ^ 2 := by
    calc
      (56231561496331 * D) * m ^ 2 = D * (56231561496331 * m ^ 2) := by ring
      _ ≤ D * (28688075015625 * sigma) := Nat.mul_le_mul_left D hcross
      _ = 28688075015625 * (D * sigma) := by ring
      _ = 28688075015625 * (p * m ^ 2) := by rw [hrel]
      _ = (28688075015625 * p) * m ^ 2 := by ring
  have hcoef := Nat.le_of_mul_le_mul_right hineq hmpos
  rcases hcases with h3 | h9 | h15 | h27 | h45 | h69 | h75
  · omega
  · omega
  · omega
  · exact Or.inl h27
  · exact Or.inr (Or.inl h45)
  · exact Or.inr (Or.inr (Or.inl h69))
  · exact Or.inr (Or.inr (Or.inr h75))
