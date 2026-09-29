-- Prove2me | solution 1 for OddPerfectNumber.padicVal_packaged_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T08:59:37.925626+00:00
-- url     : https://prove2.me/submissions/18708d73-cb74-4453-8a49-3fb1f78a764c

import Mathlib

-- STAGED, NOT YET SUBMITTED.
-- Bridge repair 434 ACCEPTED, validating the shared ascribed-`hmul`
-- Fact-pinning and dvd-valuation-zero steps. The remaining new shape here
-- is the `hval_pk` bounds route (push_neg + cancel to `p ∣ 1`).
theorem solution (p k d : Nat) (hp : p.Prime) (hd0 : d ≠ 0)
    (hpd : ¬ p ∣ d) : padicValNat p (p ^ k * d) = k := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hppos : 0 < p := hp.pos
  have hpk0 : p ^ k ≠ 0 := (pow_pos hppos k).ne'
  have hval_d : padicValNat p d = 0 := by
    have h1 : ¬ p ^ 1 ∣ d := by simpa using hpd
    have h2 : ¬ 1 ≤ padicValNat p d :=
      fun hle => h1 ((padicValNat_dvd_iff_le hd0).mpr hle)
    omega
  have hval_pk : padicValNat p (p ^ k) = k := by
    have hlb : k ≤ padicValNat p (p ^ k) :=
      (padicValNat_dvd_iff_le hpk0).mp (dvd_refl _)
    have hub : padicValNat p (p ^ k) ≤ k := by
      by_contra hcon
      push_neg at hcon
      have h2le : k + 1 ≤ padicValNat p (p ^ k) := by omega
      have hdvd : p ^ (k + 1) ∣ p ^ k :=
      -- NOTE (row 440 CE): the iff is `p^n ∣ a ↔ n ≤ v`, so from
      -- `k + 1 ≤ v` to a dvd goal is `.mpr`, not `.mp`.
        (padicValNat_dvd_iff_le hpk0).mpr h2le
      have hcancel : p ∣ 1 := by
      -- NOTE (row 442 CE): `simpa` does not reliably unfold `p ^ (k+1)`
      -- to `p ^ k * p`; bridge explicitly with `pow_succ`.
        have hps : p ^ (k + 1) = p ^ k * p := pow_succ p k
        have e : p ^ k * p ∣ p ^ k * 1 := by
          rw [← hps, mul_one]
          exact hdvd
        exact (mul_dvd_mul_iff_left hpk0).mp e
      exact hp.ne_one (Nat.dvd_one.mp hcancel)
    exact le_antisymm hub hlb
  have hmul : padicValNat p (p ^ k * d)
      = padicValNat p (p ^ k) + padicValNat p d :=
    padicValNat.mul hpk0 hd0
  rw [hmul, hval_pk, hval_d, add_zero]
