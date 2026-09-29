-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_seventeen_D289_q4_mod3_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T18:27:57.215323+00:00
-- url     : https://prove2.me/submissions/bbef2c72-b591-4ce1-b348-bb390c1b2044

import Mathlib
-- EXPONENT CONVENTION: a,b,c,e are HALF exponents; full exponents are twice these.
theorem solution (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 17 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 17 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2)
    (hp_eq : p = 2 * D - 1)
    (hq4gt : 17 < q4)
    (ha : 1 ≤ a)
    (hD : D = 289) :
    q4 % 3 = 1 := by
  subst hD
  have hp577 : p = 577 := by omega
  subst hp577
  have h1 : (3 : Nat) ∣ 3 ^ (2 * a) := dvd_pow_self 3 (by omega)
  have hfac2 : m ^ 2 = 3 ^ (2*a) * (5 ^ (2*b) * 17 ^ (2*c) * q4 ^ (2*e)) := by
    rw [hfac]; ring
  have h3dvd : 3 ∣ m ^ 2 := by rw [hfac2]; exact dvd_mul_of_dvd_left h1 _
  have hm0 : m ^ 2 % 3 = 0 := Nat.mod_eq_zero_of_dvd h3dvd
  have e289 : 289 % 3 = 1 := by decide
  have e577 : 577 % 3 = 1 := by decide
  have hcong : (289 * sigma) % 3 = (577 * m ^ 2) % 3 := by rw [hrel]
  have hsig0 : sigma % 3 = 0 := by
    have hL : (289 * sigma) % 3 = sigma % 3 := by simp [Nat.mul_mod, e289]
    have hR : (577 * m ^ 2) % 3 = 0 := by simp [Nat.mul_mod, e577, hm0]
    omega
  have hS3 : (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) % 3 = 1 := by
    have hsplit : (∑ i ∈ Finset.range (2*a + 1), 3 ^ i)
        = 1 + ∑ i ∈ Finset.range (2*a), 3 ^ (i+1) := by
      rw [Finset.sum_range_succ']
      simp [add_comm]
    have hz0 : (∑ i ∈ Finset.range (2*a), (3 ^ (i+1) % 3)) = 0 := by
      apply Finset.sum_eq_zero
      intro x _
      apply Nat.mod_eq_zero_of_dvd
      exact dvd_pow_self 3 (by omega : x + 1 ≠ 0)
    have hz : (∑ i ∈ Finset.range (2*a), 3 ^ (i+1)) % 3 = 0 := by
      calc (∑ i ∈ Finset.range (2*a), 3 ^ (i+1)) % 3
          = (∑ i ∈ Finset.range (2*a), (3 ^ (i+1) % 3)) % 3 := by
            rw [Finset.sum_nat_mod]
        _ = (0 : Nat) % 3 := by rw [hz0]
        _ = 0 := by decide
    have hS3done : (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) % 3 = 1 := by
      calc (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) % 3
          = (1 + ∑ i ∈ Finset.range (2*a), 3 ^ (i+1)) % 3 := by rw [hsplit]
        _ = 1 := by simp [Nat.add_mod, hz]
    exact hS3done
  have h5even : ∀ k, (5 : Nat) ^ (2*k) % 3 = 1 := by
    intro k
    induction k with
    | zero => decide
    | succ n ih =>
      have : (5 : Nat) ^ (2*(n+1)) = 25 * 5 ^ (2*n) := by
        rw [show 2*(n+1) = (2*n)+2 from by omega, pow_add]
        ring_nf
      rw [this]
      have h25 : (25 : Nat) % 3 = 1 := by decide
      simp [Nat.mul_mod, h25, ih]
  have hS5gen : ∀ n, (∑ i ∈ Finset.range (2*n + 1), (5 : Nat) ^ i) % 3 = 1 := by
    intro n
    induction n with
    | zero => decide
    | succ n ih =>
      have hexpand : (∑ i ∈ Finset.range (2*(n+1) + 1), (5 : Nat) ^ i)
          = (∑ i ∈ Finset.range (2*n + 1), 5 ^ i) + 5 ^ (2*n+1) + 5 ^ (2*n+2) := by
        rw [show 2*(n+1)+1 = (2*n+1)+2 from by omega, Finset.sum_range_add]
        simp [Finset.sum_range_succ, add_assoc]
      have ho : (5 : Nat) ^ (2*n+1) % 3 = 2 := by
        have h5n := h5even n
        have : (5 : Nat) ^ (2*n+1) = 5 * 5 ^ (2*n) := by rw [pow_succ']
        rw [this]
        simp [Nat.mul_mod, h5n]
      have he : (5 : Nat) ^ (2*n+2) % 3 = 1 := by
        have h5n := h5even n
        have : (5 : Nat) ^ (2*n+2) = 25 * 5 ^ (2*n) := by
          rw [show 2*n+2 = (2*n)+2 from by omega, pow_add]
          ring_nf
        rw [this]
        have h25 : (25 : Nat) % 3 = 1 := by decide
        simp [Nat.mul_mod, h25, h5n]
      rw [hexpand]
      simp [Nat.add_mod, ih, ho, he]
  have hS5 : (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) % 3 = 1 := hS5gen b
  have h17even : ∀ k, (17 : Nat) ^ (2*k) % 3 = 1 := by
    intro k
    induction k with
    | zero => decide
    | succ n ih =>
      have : (17 : Nat) ^ (2*(n+1)) = 289 * 17 ^ (2*n) := by
        rw [show 2*(n+1) = (2*n)+2 from by omega, pow_add]
        ring_nf
      rw [this]
      have h289 : (289 : Nat) % 3 = 1 := by decide
      simp [Nat.mul_mod, h289, ih]
  have hS17gen : ∀ n, (∑ i ∈ Finset.range (2*n + 1), (17 : Nat) ^ i) % 3 = 1 := by
    intro n
    induction n with
    | zero => decide
    | succ n ih =>
      have hexpand : (∑ i ∈ Finset.range (2*(n+1) + 1), (17 : Nat) ^ i)
          = (∑ i ∈ Finset.range (2*n + 1), 17 ^ i) + 17 ^ (2*n+1) + 17 ^ (2*n+2) := by
        rw [show 2*(n+1)+1 = (2*n+1)+2 from by omega, Finset.sum_range_add]
        simp [Finset.sum_range_succ, add_assoc]
      have ho : (17 : Nat) ^ (2*n+1) % 3 = 2 := by
        have h17n := h17even n
        have : (17 : Nat) ^ (2*n+1) = 17 * 17 ^ (2*n) := by rw [pow_succ']
        rw [this]
        simp [Nat.mul_mod, h17n]
      have he : (17 : Nat) ^ (2*n+2) % 3 = 1 := by
        have h17n := h17even n
        have : (17 : Nat) ^ (2*n+2) = 289 * 17 ^ (2*n) := by
          rw [show 2*n+2 = (2*n)+2 from by omega, pow_add]
          ring_nf
        rw [this]
        have h289 : (289 : Nat) % 3 = 1 := by decide
        simp [Nat.mul_mod, h289, h17n]
      rw [hexpand]
      simp [Nat.add_mod, ih, ho, he]
  have hS17 : (∑ i ∈ Finset.range (2*c + 1), 17 ^ i) % 3 = 1 := hS17gen c
  have hSq4 : (∑ i ∈ Finset.range (2*e + 1), q4 ^ i) % 3 = 0 := by
    have m3 : (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) ≡ 1 [MOD 3] := hS3
    have m5 : (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) ≡ 1 [MOD 3] := hS5
    have m17 : (∑ i ∈ Finset.range (2*c + 1), 17 ^ i) ≡ 1 [MOD 3] := hS17
    have mP : ((∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
        (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
        (∑ i ∈ Finset.range (2*c + 1), 17 ^ i)) ≡ 1 * 1 * 1 [MOD 3] :=
      (m3.mul m5).mul m17
    have hsig0prod : (((∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
        (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
        (∑ i ∈ Finset.range (2*c + 1), 17 ^ i)) *
        (∑ i ∈ Finset.range (2*e + 1), q4 ^ i)) % 3 = 0 := by
      rw [← hsigma]; exact hsig0
    have mQ : (((∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
        (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
        (∑ i ∈ Finset.range (2*c + 1), 17 ^ i)) *
        (∑ i ∈ Finset.range (2*e + 1), q4 ^ i)) ≡
        (1 * 1 * 1) * (∑ i ∈ Finset.range (2*e + 1), q4 ^ i) [MOD 3] :=
      mP.mul (Nat.ModEq.refl (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    have hfin : ((1 * 1 * 1) * (∑ i ∈ Finset.range (2*e + 1), q4 ^ i)) % 3 = 0 := by
      rw [← mQ]; exact hsig0prod
    simpa using hfin
  have hq4mod : q4 % 3 = 0 ∨ q4 % 3 = 1 ∨ q4 % 3 = 2 := by omega
  rcases hq4mod with h0 | h1 | h2
  · have hS : (∑ i ∈ Finset.range (2*e + 1), q4 ^ i) % 3 = 1 := by
      have hgen : ∀ n, (∑ i ∈ Finset.range n, q4 ^ (i+1)) % 3 = 0 := by
        intro n
        induction n with
        | zero => simp
        | succ n ih =>
          rw [Finset.sum_range_succ]
          have hx0 : q4 ^ (n+1) % 3 = 0 := by
            have hqm : q4 % 3 = 0 := h0
            have hpow : q4 ^ (n+1) % 3 = (q4 % 3) ^ (n+1) % 3 := by rw [Nat.pow_mod]
            rw [hpow, hqm]
            simp [hpow, hqm]
          simp [Nat.add_mod, ih, hx0]
      have hsplit : (∑ i ∈ Finset.range (2*e + 1), q4 ^ i)
          = 1 + ∑ i ∈ Finset.range (2*e), q4 ^ (i+1) := by
        rw [Finset.sum_range_succ']
        simp [add_comm]
      simp [hsplit, Nat.add_mod, hgen]
    omega
  · exact h1
  · have hqe : ∀ k, (q4 : Nat) ^ (2*k) % 3 = 1 := by
      intro k
      induction k with
      | zero => simp
      | succ n ih =>
        have h4 : (q4 : Nat) ^ 2 % 3 = 1 := by
          have hpow : q4 ^ 2 % 3 = (q4 % 3) ^ 2 % 3 := by rw [Nat.pow_mod]
          rw [hpow, h2]
          decide
        have : (q4 : Nat) ^ (2*(n+1)) = q4 ^ 2 * q4 ^ (2*n) := by
          rw [show 2*(n+1) = (2*n)+2 from by omega, pow_add]
          ring_nf
        rw [this]
        simp [Nat.mul_mod, h4, ih]
    have hSgen : ∀ n, (∑ i ∈ Finset.range (2*n + 1), q4 ^ i) % 3 = 1 := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        have hexpand : (∑ i ∈ Finset.range (2*(n+1) + 1), q4 ^ i)
            = (∑ i ∈ Finset.range (2*n + 1), q4 ^ i) + q4 ^ (2*n+1) + q4 ^ (2*n+2) := by
          rw [show 2*(n+1)+1 = (2*n+1)+2 from by omega, Finset.sum_range_add]
          simp [Finset.sum_range_succ, add_assoc]
        have hqn := hqe n
        have ho : q4 ^ (2*n+1) % 3 = 2 := by
          have : q4 ^ (2*n+1) = q4 * q4 ^ (2*n) := by rw [pow_succ']
          rw [this]
          simp [Nat.mul_mod, hqn, h2]
        have he : q4 ^ (2*n+2) % 3 = 1 := by
          have h4 : (q4 : Nat) ^ 2 % 3 = 1 := by
            have hpow : q4 ^ 2 % 3 = (q4 % 3) ^ 2 % 3 := by rw [Nat.pow_mod]
            rw [hpow, h2]
            decide
          have : q4 ^ (2*n+2) = q4 ^ 2 * q4 ^ (2*n) := by
            rw [show 2*n+2 = (2*n)+2 from by omega, pow_add]
            ring_nf
          rw [this]
          simp [Nat.mul_mod, h4, hqn]
        rw [hexpand]
        simp [Nat.add_mod, ih, ho, he]
    have hS : (∑ i ∈ Finset.range (2*e + 1), q4 ^ i) % 3 = 1 := hSgen e
    omega
