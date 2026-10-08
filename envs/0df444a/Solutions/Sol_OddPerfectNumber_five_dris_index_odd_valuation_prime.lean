-- Prove2me | solution 1 for OddPerfectNumber.five_dris_index_odd_valuation_prime
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-05T18:20:16.269913+00:00
-- url     : https://prove2.me/submissions/fa498c55-29cb-41a4-b2ed-95b9e2fde956

import Mathlib

theorem solution (p m s : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hs : 0 < s)
    (heq : 2 * m ^ 2 = (∑ d ∈ (p ^ 5).divisors, d) * s) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ≠ 3 ∧ ℓ ∣ p ^ 4 + p ^ 2 + 1 ∧ Odd (padicValNat ℓ s) := by
  obtain ⟨j, hj⟩ : ∃ j, p = 2 * j + 1 := by
    rcases hp.eq_two_or_odd' with h | h
    · exact absurd h hp2
    · exact h
  have hj1 : 1 ≤ j := by
    have := hp.two_le
    omega
  have hsig : (∑ d ∈ (p ^ 5).divisors, d) = 2 * ((j + 1) * ((4 * j ^ 2 + 6 * j + 3) *
      (4 * j ^ 2 + 2 * j + 1))) := by
    rw [Nat.sum_divisors_prime_pow hp]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, zero_add, pow_one]
    subst hj
    ring
  set A := j + 1 with hA
  set B := 4 * j ^ 2 + 6 * j + 3 with hB
  set C := 4 * j ^ 2 + 2 * j + 1 with hC
  have hm : m ^ 2 = A * B * C * s := by
    rw [hsig] at heq
    have : 2 * m ^ 2 = 2 * (A * B * C * s) := by rw [heq]; ring
    omega
  have hBC : B * C = p ^ 4 + p ^ 2 + 1 := by subst hj; simp only [hB, hC]; ring
  have hApos : 0 < A := by omega
  have hBpos : 0 < B := by omega
  have hCpos : 0 < C := by omega
  -- B and C are not squares
  have hBns : ∀ d, B ≠ d ^ 2 := by
    intro d hd
    have h1 : (2 * j + 1) ^ 2 < d ^ 2 := by rw [← hd, hB]; nlinarith
    have h2 : d ^ 2 < (2 * j + 2) ^ 2 := by rw [← hd, hB]; nlinarith
    have h1' := (Nat.pow_lt_pow_iff_left (by norm_num)).mp h1
    have h2' := (Nat.pow_lt_pow_iff_left (by norm_num)).mp h2
    omega
  have hCns : ∀ d, C ≠ d ^ 2 := by
    intro d hd
    have h1 : (2 * j) ^ 2 < d ^ 2 := by rw [← hd, hC]; nlinarith
    have h2 : d ^ 2 < (2 * j + 1) ^ 2 := by rw [← hd, hC]; nlinarith
    have h1' := (Nat.pow_lt_pow_iff_left (by norm_num)).mp h1
    have h2' := (Nat.pow_lt_pow_iff_left (by norm_num)).mp h2
    omega
  -- coprimality
  have hCp1 : Nat.Coprime C p := by
    have : C = 1 + (2 * j + 1) * (2 * j) := by rw [hC]; ring
    rw [this, hj]; simp [Nat.coprime_add_mul_left_left]
  have hC2 : Nat.Coprime C 2 := by
    have : C = 1 + 2 * (2 * j ^ 2 + j) := by rw [hC]; ring
    rw [this]; simp
  have hCp : Nat.Coprime C (2 * p) := Nat.Coprime.mul_right hC2 hCp1
  have hBC_cop : Nat.Coprime B C := by
    have : B = C + (2 * p) * 1 := by rw [hB, hC, hj]; ring
    rw [this]; simpa [Nat.coprime_comm] using hCp.symm
  have hBA : Nat.Coprime B A := by
    have : B = 1 + (j + 1) * (4 * j + 2) := by rw [hB]; ring
    rw [this, hA]; simp
  have hCA : ¬ 3 ∣ C → Nat.Coprime C A := by
    intro h3
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    have e : C = 3 + A * (4 * i + 2) := by rw [hA, hC]; ring
    have hg : Nat.gcd C A ∣ 3 := by
      have h1 : Nat.gcd C A ∣ 3 + A * (4 * i + 2) := e ▸ Nat.gcd_dvd_left _ _
      have h2 : Nat.gcd C A ∣ A * (4 * i + 2) := dvd_mul_of_dvd_left (Nat.gcd_dvd_right _ _) _
      exact (Nat.dvd_add_left h2).mp h1
    rcases (Nat.dvd_prime Nat.prime_three).mp hg with h | h
    · exact h
    · exfalso; apply h3; rw [← h]; exact Nat.gcd_dvd_left _ _
  -- key step: a non-square X prime to 3, prime to A and Z, divides m² = X (A Z s)
  have key : ∀ X Z : ℕ, 0 < X → 0 < Z → ¬ 3 ∣ X → (∀ d, X ≠ d ^ 2) → Nat.Coprime X A →
      Nat.Coprime X Z → m ^ 2 = X * (A * Z * s) → X ∣ B * C →
      ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ≠ 3 ∧ ℓ ∣ p ^ 4 + p ^ 2 + 1 ∧ Odd (padicValNat ℓ s) := by
    intro X Z hX hZ h3 hns hXA hXZ hmX hXd
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
    refine ⟨ℓ, hℓ, ?_, ?_, ?_⟩
    · rintro rfl; exact h3 hℓX
    · rw [← hBC]; exact dvd_trans hℓX hXd
    · exact ⟨padicValNat ℓ m - padicValNat ℓ b - 1, by omega⟩
  by_cases h3C : 3 ∣ C
  · have h3B : ¬ 3 ∣ B := by
      intro h3B
      have := Nat.dvd_gcd h3B h3C
      rw [hBC_cop] at this
      omega
    exact key B C hBpos hCpos h3B hBns hBA hBC_cop (by rw [hm]; ring) (dvd_mul_right _ _)
  · exact key C B hCpos hBpos h3C hCns (hCA h3C) hBC_cop.symm (by rw [hm]; ring)
      (dvd_mul_left _ _)
