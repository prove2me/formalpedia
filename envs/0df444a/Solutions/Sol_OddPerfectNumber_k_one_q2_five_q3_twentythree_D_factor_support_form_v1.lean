-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentythree_D_factor_support_form_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-16T19:59:51.350227+00:00
-- url     : https://prove2.me/submissions/63e0e021-2bbe-442e-9a43-0b7a9263b1d6

import Mathlib

theorem solution (m a b c e D q4 : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 23 ^ (2*c) * q4 ^ (2*e))
    (hDdvd : D ∣ m ^ 2) (hDpos : 0 < D)
    (hq4prime : q4.Prime) (hq4gt : 23 < q4)
    (hDsupport : ∀ r, r.Prime → r ∣ D →
      r = 3 ∨ r = 5 ∨ r = 23 ∨ r = q4) :
    ∃ i j k l, D = 3^i * 5^j * 23^k * q4^l ∧
      i ≤ 2*a ∧ j ≤ 2*b ∧ k ≤ 2*c ∧ l ≤ 2*e := by
  let i := D.factorization 3
  let j := D.factorization 5
  let k := D.factorization 23
  let l := D.factorization q4
  have hq43 : q4 ≠ 3 := by omega
  have hq45 : q4 ≠ 5 := by omega
  have hq423 : q4 ≠ 23 := by omega
  have h3p : Nat.Prime 3 := by norm_num
  have h5p : Nat.Prime 5 := by norm_num
  have h23p : Nat.Prime 23 := by norm_num
  have hDne : D ≠ 0 := Nat.ne_of_gt hDpos
  have hmne : m ^ 2 ≠ 0 := by
    rw [hfac]
    positivity
  have hle : D.factorization ≤ (m ^ 2).factorization :=
    (Nat.factorization_le_iff_dvd hDne hmne).2 hDdvd
  have hzero : ∀ r, r ≠ 3 → r ≠ 5 → r ≠ 23 → r ≠ q4 →
      D.factorization r = 0 := by
    intro r hr3 hr5 hr23 hrq
    by_cases hrp : r.Prime
    · by_cases hrd : r ∣ D
      · rcases hDsupport r hrp hrd with h | h | h | h
        · exact False.elim (hr3 h)
        · exact False.elim (hr5 h)
        · exact False.elim (hr23 h)
        · exact False.elim (hrq h)
      · exact (Nat.factorization_eq_zero_iff D r).2 (Or.inr (Or.inl hrd))
    · exact (Nat.factorization_eq_zero_iff D r).2 (Or.inl hrp)
  let f : Nat →₀ Nat :=
    Finsupp.single 3 i + Finsupp.single 5 j +
      Finsupp.single 23 k + Finsupp.single q4 l
  have hfd : f = D.factorization := by
    ext r
    by_cases h3 : r = 3
    · subst r
      simp [f, i, j, k, l, hq43]
    · by_cases h5 : r = 5
      · subst r
        simp [f, i, j, k, l, hq45]
      · by_cases h23 : r = 23
        · subst r
          simp [f, i, j, k, l, hq423]
        · by_cases hq : r = q4
          · subst r
            simp [f, i, j, k, l, hq43, hq45, hq423]
          · simp only [f, Finsupp.add_apply, Finsupp.single_apply]
            have h3' : 3 ≠ r := by omega
            have h5' : 5 ≠ r := by omega
            have h23' : 23 ≠ r := by omega
            have hq' : q4 ≠ r := by omega
            simp [h3, h5, h23, hq, h3', h5', h23', hq',
              hzero r h3 h5 h23 hq]
  have hprod : f.prod (fun r n => r ^ n) = D := by
    calc
      f.prod (fun r n => r ^ n) = D.factorization.prod (fun r n => r ^ n) := by rw [hfd]
      _ = D := Nat.prod_factorization_pow_eq_self hDne
  have hform : D = 3^i * 5^j * 23^k * q4^l := by
    simpa [f, Finsupp.prod_add_index', Nat.pow_add] using hprod.symm
  have hfac3 : (m ^ 2).factorization 3 = 2*a := by
    rw [hfac]
    rw [Nat.factorization_mul (by positivity) (by positivity)]
    rw [Nat.factorization_mul (by positivity) (by positivity)]
    rw [Nat.factorization_mul (by positivity) (by positivity)]
    rw [h3p.factorization_pow, h5p.factorization_pow,
      h23p.factorization_pow, hq4prime.factorization_pow]
    simp [hq43, hq45, hq423]
  have hfac5 : (m ^ 2).factorization 5 = 2*b := by
    rw [hfac]
    rw [Nat.factorization_mul (by positivity) (by positivity)]
    rw [Nat.factorization_mul (by positivity) (by positivity)]
    rw [Nat.factorization_mul (by positivity) (by positivity)]
    rw [h3p.factorization_pow, h5p.factorization_pow,
      h23p.factorization_pow, hq4prime.factorization_pow]
    simp [hq43, hq45, hq423]
  have hfac23 : (m ^ 2).factorization 23 = 2*c := by
    rw [hfac]
    rw [Nat.factorization_mul (by positivity) (by positivity)]
    rw [Nat.factorization_mul (by positivity) (by positivity)]
    rw [Nat.factorization_mul (by positivity) (by positivity)]
    rw [h3p.factorization_pow, h5p.factorization_pow,
      h23p.factorization_pow, hq4prime.factorization_pow]
    simp [hq43, hq45, hq423]
  have hfacq : (m ^ 2).factorization q4 = 2*e := by
    rw [hfac]
    rw [Nat.factorization_mul (by positivity) (by positivity)]
    rw [Nat.factorization_mul (by positivity) (by positivity)]
    rw [Nat.factorization_mul (by positivity) (by positivity)]
    rw [h3p.factorization_pow, h5p.factorization_pow,
      h23p.factorization_pow, hq4prime.factorization_pow]
    simp [hq43, hq45, hq423]
  have hi : i ≤ 2*a := by
    have h := hle 3
    rw [hfac3] at h
    simpa [i] using h
  have hj : j ≤ 2*b := by
    have h := hle 5
    rw [hfac5] at h
    simpa [j] using h
  have hk : k ≤ 2*c := by
    have h := hle 23
    rw [hfac23] at h
    simpa [k] using h
  have hl : l ≤ 2*e := by
    have h := hle q4
    rw [hfacq] at h
    simpa [l] using h
  exact ⟨i, j, k, l, hform, hi, hj, hk, hl⟩
