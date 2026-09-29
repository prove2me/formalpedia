-- Prove2me | solution 1 for OddPerfectNumber.k_one_phi_three_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T07:46:04.905013+00:00
-- url     : https://prove2.me/submissions/11e6a0cc-383f-4f47-bfe3-e093b3dc78b0

import Mathlib

theorem solution (p q : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hq : q.Prime)
    (hdiv : q ∣ (p + 1) / 2) :
    ¬ p ∣ q ^ 2 + q + 1 := by
  -- Write `(p+1)/2 = q * r` and set `k = 2 * r`, so `q * k = p + 1`.
  -- `obtain` consumes `hdiv`; keep a copy for the later size facts.
  have hdiv_copy := hdiv
  obtain ⟨r, hr⟩ := hdiv
  set k := 2 * r with hk
  have hp1 : 1 < p := hp.one_lt
  have hqpos : 0 < q := hq.pos
  have htpos : 0 < (p + 1) / 2 := by omega
  have hq_le_t : q ≤ (p + 1) / 2 := Nat.le_of_dvd htpos hdiv_copy
  have hq_lt_p : q < p := by omega
  have ht_odd : (p + 1) / 2 % 2 = 1 := by omega
  -- `q` is odd: an even divisor would force `(p+1)/2` even.
  have hq_odd : q % 2 = 1 := by
    by_contra h
    have h2q : 2 ∣ q := by omega
    have h2t : 2 ∣ (p + 1) / 2 := dvd_trans h2q hdiv_copy
    omega
  have hq3 : 3 ≤ q := by
    have h2 := hq.two_le
    omega
  have hr0 : r ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hr
    omega
  have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
  have hk2ge : 2 ≤ k := by omega
  -- `q * k = p + 1`: halve `(p+1)/2` exactly using `p % 4 = 1`.
  have hpk : q * k = p + 1 := by
    rw [hk]
    have e : q * (2 * r) = 2 * (q * r) := by ring
    rw [e, ← hr]
    omega
  -- Key identity: `q * (q + k + 1) = (q^2 + q + 1) + p`.
  have hident : q * (q + k + 1) = (q ^ 2 + q + 1) + p := by
    have e1 : q * (q + k + 1) = q * q + q * k + q := by ring
    rw [e1, hpk]
    ring
  intro hN
  have hqS : p ∣ q * (q + k + 1) := by
    rw [hident]
    exact dvd_add hN (dvd_refl p)
  -- Euclid: `p ∣ q` (impossible, `q < p`) or `p ∣ q + k + 1`.
  have hpq : ¬ p ∣ q := by
    intro h
    have hle := Nat.le_of_dvd hqpos h
    omega
  rcases (hp.dvd_mul).mp hqS with hqp | hSdiv
  · exact absurd hqp hpq
  · -- Hence `q * k ≤ q + k + 2`, i.e. `(q-1)(k-1) ≤ 3`.
    have hposS : 0 < q + k + 1 := by omega
    have hple : p ≤ q + k + 1 := Nat.le_of_dvd hposS hSdiv
    have hS : q * k ≤ q + k + 2 := by
      have h1 : p + 1 ≤ (q + k + 1) + 1 := by omega
      rw [← hpk] at h1
      omega
    rcases lt_or_ge k 3 with h | h
    · -- Small case `k = 2`: then `q = 3`, `p = 5`, but `5 ∤ 13`.
      have hk2 : k = 2 := by omega
      have hq4 : q ≤ 4 := by
        rw [hk2] at hS
        omega
      have hq_eq : q = 3 := by omega
      have hp5 : p = 5 := by
        have h2 := hpk
        rw [hk2, hq_eq] at h2
        omega
      rw [hp5, hq_eq] at hN
      omega
    · -- Main case `k ≥ 3`: two linearizable sub-cases.
      by_cases hc : q + 3 ≤ 2 * k
      · have e1 : q + k + 3 ≤ 3 * k := by omega
        have e2 : 3 * k ≤ q * k := mul_le_mul_left hq3 k
        omega
      · have h2 : 2 * k ≤ q + 2 := by omega
        have e1 : q + k + 3 ≤ 3 * q := by omega
        -- NB: `mul_le_mul_right` concludes `q * 3`, not `3 * q`;
        -- state it verbatim so `omega` sees shared atoms.
        have e2 : q * 3 ≤ q * k := mul_le_mul_right h q
        omega
