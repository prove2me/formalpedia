-- Prove2me | solution 1 for OddPerfectNumber.nine_dris_index_odd_valuation_prime
-- status  : ACCEPTED   (prove)
-- author  : @Himan
-- created : 2026-11-15T04:01:03.707757+00:00
-- url     : https://prove2.me/submissions/5d45dbed-8f73-42f2-aa22-ce27e4862a9a

import Mathlib

theorem solution (p m s : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hs : 0 < s)
    (heq : 2 * m ^ 2 = (∑ d ∈ (p ^ 9).divisors, d) * s) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ % 10 = 1 ∧ ℓ ∣ p ^ 8 + p ^ 6 + p ^ 4 + p ^ 2 + 1 ∧
      Odd (padicValNat ℓ s) := by
  obtain ⟨j, hj⟩ : ∃ j, p = 2 * j + 1 := by
    rcases hp.eq_two_or_odd' with h | h
    · exact absurd h hp2
    · exact h
  have hj1 : 1 ≤ j := by
    have := hp.two_le
    omega
  -- σ(p^9) = (p+1) Φ₅(p) Φ₁₀(p) = 2 (j+1) B C
  have hsig : (∑ d ∈ (p ^ 9).divisors, d) = 2 * ((j + 1) *
      ((16 * j ^ 4 + 40 * j ^ 3 + 40 * j ^ 2 + 20 * j + 5) *
        (16 * j ^ 4 + 24 * j ^ 3 + 16 * j ^ 2 + 4 * j + 1))) := by
    rw [Nat.sum_divisors_prime_pow hp]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, zero_add, pow_one]
    subst hj
    ring
  set A := j + 1 with hA
  set B := 16 * j ^ 4 + 40 * j ^ 3 + 40 * j ^ 2 + 20 * j + 5 with hB
  set C := 16 * j ^ 4 + 24 * j ^ 3 + 16 * j ^ 2 + 4 * j + 1 with hC
  have hm : m ^ 2 = A * B * C * s := by
    rw [hsig] at heq
    have : 2 * m ^ 2 = 2 * (A * B * C * s) := by rw [heq]; ring
    omega
  have hBC : B * C = p ^ 8 + p ^ 6 + p ^ 4 + p ^ 2 + 1 := by
    subst hj; simp only [hB, hC]; ring
  have hApos : 0 < A := by omega
  have hBpos : 0 < B := by omega
  have hCpos : 0 < C := by omega
  -- C = Φ₁₀(p) is never a square
  have hCns : ∀ d, C ≠ d ^ 2 := by
    intro d hd
    have h1 : (8 * j ^ 2 + 6 * j + 1) ^ 2 < (2 * d) ^ 2 := by
      have : (2 * d) ^ 2 = 4 * C := by rw [hd]; ring
      rw [this, hC]; nlinarith
    have h2 : (2 * d) ^ 2 < (8 * j ^ 2 + 6 * j + 2) ^ 2 := by
      have : (2 * d) ^ 2 = 4 * C := by rw [hd]; ring
      rw [this, hC]; nlinarith
    have h1' := (Nat.pow_lt_pow_iff_left (by norm_num)).mp h1
    have h2' := (Nat.pow_lt_pow_iff_left (by norm_num)).mp h2
    omega
  -- B = Φ₅(p) is a square only for p = 3
  have hBns : j ≠ 1 → ∀ d, B ≠ d ^ 2 := by
    intro hj' d hd
    have h4 : (2 * d) ^ 2 = 4 * B := by rw [hd]; ring
    have h1 : (8 * j ^ 2 + 10 * j + 3) ^ 2 < (2 * d) ^ 2 := by
      rw [h4, hB]; nlinarith
    have h2 : (2 * d) ^ 2 < (8 * j ^ 2 + 10 * j + 5) ^ 2 := by
      rw [h4, hB]; nlinarith
    have h1' := (Nat.pow_lt_pow_iff_left (by norm_num)).mp h1
    have h2' := (Nat.pow_lt_pow_iff_left (by norm_num)).mp h2
    have hd' : d = 4 * j ^ 2 + 5 * j + 2 := by omega
    rw [hd', hB] at hd
    have hsq1 : (j : ℤ) ^ 2 = 1 := by
      have hdz : (16 * (j : ℤ) ^ 4 + 40 * (j : ℤ) ^ 3 + 40 * (j : ℤ) ^ 2 + 20 * (j : ℤ) + 5) =
          (4 * (j : ℤ) ^ 2 + 5 * (j : ℤ) + 2) ^ 2 := by exact_mod_cast hd
      linear_combination (-1 : ℤ) * hdz
    have hjj : j ^ 2 = 1 := by exact_mod_cast hsq1
    have : j = 1 := by
      rcases Nat.lt_or_ge j 2 with h | h
      · omega
      · nlinarith
    exact hj' this
  -- coprimality
  have hCp1 : Nat.Coprime C p := by
    have : C = 1 + (2 * j + 1) * (8 * j ^ 3 + 8 * j ^ 2 + 4 * j) := by rw [hC]; ring
    rw [this, hj]; simp [Nat.coprime_add_mul_left_left]
  have hC2 : Nat.Coprime C 2 := by
    have : C = 1 + 2 * (8 * j ^ 4 + 12 * j ^ 3 + 8 * j ^ 2 + 2 * j) := by rw [hC]; ring
    rw [this]; simp
  have hCq : Nat.Coprime C (p ^ 2 + 1) := by
    have : C = 1 + (p ^ 2 + 1) * (4 * j ^ 2 + 2 * j) := by rw [hC, hj]; ring
    rw [this]; simp
  have hCp : Nat.Coprime C (2 * p * (p ^ 2 + 1)) :=
    Nat.Coprime.mul_right (Nat.Coprime.mul_right hC2 hCp1) hCq
  have hBC_cop : Nat.Coprime B C := by
    have : B = C + (2 * p * (p ^ 2 + 1)) * 1 := by rw [hB, hC, hj]; ring
    rw [this]; simpa [Nat.coprime_comm] using hCp.symm
  have hBA : Nat.Coprime B A := by
    have : B = 1 + (j + 1) * (16 * j ^ 3 + 24 * j ^ 2 + 16 * j + 4) := by rw [hB]; ring
    rw [this, hA]; simp
  have hCA : ¬ 5 ∣ C → Nat.Coprime C A := by
    intro h5
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    have e : C = 5 + A * (16 * i ^ 3 + 56 * i ^ 2 + 72 * i + 28) := by rw [hA, hC]; ring
    have hg : Nat.gcd C A ∣ 5 := by
      have h1 : Nat.gcd C A ∣ 5 + A * (16 * i ^ 3 + 56 * i ^ 2 + 72 * i + 28) :=
        e ▸ Nat.gcd_dvd_left _ _
      have h2 : Nat.gcd C A ∣ A * (16 * i ^ 3 + 56 * i ^ 2 + 72 * i + 28) :=
        dvd_mul_of_dvd_left (Nat.gcd_dvd_right _ _) _
      exact (Nat.dvd_add_left h2).mp h1
    rcases (Nat.dvd_prime Nat.prime_five).mp hg with h | h
    · exact h
    · exfalso; apply h5; rw [← h]; exact Nat.gcd_dvd_left _ _
  -- a prime ℓ ≠ 5 dividing Φ₅(p²) is ≡ 1 (mod 10)
  have hmod : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 5 → ℓ ∣ p ^ 8 + p ^ 6 + p ^ 4 + p ^ 2 + 1 →
      ℓ % 10 = 1 := by
    intro ℓ hℓ hℓ5 hdvd
    have : Fact ℓ.Prime := ⟨hℓ⟩
    have hodd : ℓ ≠ 2 := by
      rintro rfl
      have : (p ^ 8 + p ^ 6 + p ^ 4 + p ^ 2 + 1) % 2 = 1 := by
        have hp1 : p % 2 = 1 := by omega
        simp [Nat.add_mod, Nat.pow_mod, hp1]
      omega
    have hz : ((p : ZMod ℓ) ^ 2) ^ 4 + ((p : ZMod ℓ) ^ 2) ^ 3 + ((p : ZMod ℓ) ^ 2) ^ 2 +
        (p : ZMod ℓ) ^ 2 + 1 = 0 := by
      have h0 : ((p ^ 8 + p ^ 6 + p ^ 4 + p ^ 2 + 1 : ℕ) : ZMod ℓ) = 0 :=
        (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
      push_cast at h0
      rw [← h0]; ring
    set x : ZMod ℓ := (p : ZMod ℓ) ^ 2 with hx
    have hx5 : x ^ 5 = 1 := by
      have : x ^ 5 - 1 = (x - 1) * (x ^ 4 + x ^ 3 + x ^ 2 + x + 1) := by ring
      rw [hz, mul_zero] at this
      exact sub_eq_zero.mp this
    have hx1 : x ≠ 1 := by
      intro h1
      rw [h1] at hz
      have h5 : ((5 : ℕ) : ZMod ℓ) = 0 := by
        push_cast; rw [← hz]; norm_num
      have := (ZMod.natCast_eq_zero_iff _ _).mp h5
      exact hℓ5 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_five).mp this)
    have hord : orderOf x = 5 := by
      haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
      exact orderOf_eq_prime hx5 hx1
    have hx0 : x ≠ 0 := by
      intro h0
      rw [h0] at hx5
      simp at hx5
    have hdiv : 5 ∣ ℓ - 1 := by
      rw [← hord]
      exact orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one hx0)
    have h2 := hℓ.two_le
    rcases hℓ.eq_two_or_odd with h | h
    · exact absurd h hodd
    · omega
  -- key step: a non-square X prime to 5, prime to A and Z, divides m² = X (A Z s)
  have key : ∀ X Z : ℕ, 0 < X → 0 < Z → ¬ 5 ∣ X → (∀ d, X ≠ d ^ 2) → Nat.Coprime X A →
      Nat.Coprime X Z → m ^ 2 = X * (A * Z * s) → X ∣ B * C →
      ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ % 10 = 1 ∧ ℓ ∣ p ^ 8 + p ^ 6 + p ^ 4 + p ^ 2 + 1 ∧
        Odd (padicValNat ℓ s) := by
    intro X Z hX hZ h5 hns hXA hXZ hmX hXd
    obtain ⟨a, b, ha, hb, hab, hsq⟩ := Nat.sq_mul_squarefree_of_pos hX
    have ha1 : a ≠ 1 := by
      rintro rfl
      exact hns b (by rw [← hab]; ring)
    obtain ⟨ℓ, hℓ, hℓa⟩ := Nat.exists_prime_and_dvd ha1
    have : Fact ℓ.Prime := ⟨hℓ⟩
    have hva : padicValNat ℓ a = 1 := by
      have hle : (a.factorization) ℓ ≤ 1 := hsq.natFactorization_le_one ℓ
      have hpos : 0 < (a.factorization) ℓ := hℓ.factorization_pos_of_dvd ha.ne' hℓa
      rw [Nat.factorization_def a hℓ] at hle hpos
      omega
    have hℓX : ℓ ∣ X := by rw [← hab]; exact dvd_mul_of_dvd_right hℓa _
    have hℓA : ¬ ℓ ∣ A := fun h => hℓ.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hXA hℓX h)
    have hℓZ : ¬ ℓ ∣ Z := fun h => hℓ.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hXZ hℓX h)
    have hAv : padicValNat ℓ A = 0 := padicValNat.eq_zero_of_not_dvd hℓA
    have hZv : padicValNat ℓ Z = 0 := padicValNat.eq_zero_of_not_dvd hℓZ
    have hXv : padicValNat ℓ X = 2 * padicValNat ℓ b + 1 := by
      rw [← hab, padicValNat.mul (by positivity) ha.ne', padicValNat.pow b 2, hva]
    have hmpos : 0 < m := by
      by_contra h0
      have : m = 0 := by omega
      rw [this] at hmX
      have : 0 < X * (A * Z * s) := by positivity
      omega
    have hv : 2 * padicValNat ℓ m = padicValNat ℓ X + padicValNat ℓ s := by
      have := congrArg (padicValNat ℓ) hmX
      rw [padicValNat.pow m 2, padicValNat.mul hX.ne' (by positivity),
        padicValNat.mul (by positivity) hs.ne', padicValNat.mul hApos.ne' hZ.ne', hAv, hZv] at this
      omega
    have hℓS : ℓ ∣ p ^ 8 + p ^ 6 + p ^ 4 + p ^ 2 + 1 := by
      rw [← hBC]; exact dvd_trans hℓX hXd
    have hℓ5 : ℓ ≠ 5 := by rintro rfl; exact h5 hℓX
    refine ⟨ℓ, hℓ, hmod ℓ hℓ hℓ5 hℓS, hℓS, ?_⟩
    exact ⟨padicValNat ℓ m - padicValNat ℓ b - 1, by omega⟩
  by_cases h5C : 5 ∣ C
  · have h5B : ¬ 5 ∣ B := by
      intro h5B
      have := Nat.dvd_gcd h5B h5C
      rw [hBC_cop] at this
      omega
    have hj' : j ≠ 1 := by
      rintro rfl
      norm_num [hC] at h5C
    exact key B C hBpos hCpos h5B (hBns hj') hBA hBC_cop (by rw [hm]; ring) (dvd_mul_right _ _)
  · exact key C B hCpos hBpos h5C hCns (hCA h5C) hBC_cop.symm (by rw [hm]; ring)
      (dvd_mul_left _ _)
