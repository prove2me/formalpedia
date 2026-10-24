-- Prove2me | solution 1 for RamanujanLostNotebook.PartIV.eq_15_3_7
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T01:56:37.302723+00:00
-- url     : https://prove2.me/submissions/98ea8c2c-648b-42c1-afea-91b125c8c26e

import Mathlib

open Complex Finset

namespace G15

lemma prod_range_sub (n : ℕ) (hn : 0 < n) {ω : ℂ} (hω : IsPrimitiveRoot ω n) (x y : ℂ) :
    x ^ n - y ^ n = ∏ k ∈ range n, (x - ω ^ k * y) := by
  rw [IsPrimitiveRoot.pow_sub_pow_eq_prod_sub_mul (R := ℂ) (x := x) (y := y) hn hω]
  have : NeZero n := ⟨hn.ne'⟩
  refine (Finset.prod_nbij (fun k => ω ^ k) (fun k hk => ?_) (fun i hi j hj h => ?_)
    (fun ξ hξ => ?_) (fun _ _ => rfl)).symm
  · rw [Polynomial.mem_nthRootsFinset hn, ← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow]
  · exact hω.pow_inj (mem_range.1 hi) (mem_range.1 hj) h
  · rw [Finset.mem_coe, Polynomial.mem_nthRootsFinset hn] at hξ
    obtain ⟨i, hi, rfl⟩ := hω.eq_pow_of_pow_eq_one hξ
    exact ⟨i, by simpa using hi, rfl⟩

end G15

open Complex Finset
open scoped Real

namespace G15

lemma sin_mul_eq (θ : ℂ) : sin θ * (2 * I * exp (θ * I)) = exp (2 * θ * I) - 1 := by
  rw [sin, show 2 * θ * I = θ * I + θ * I by ring, exp_add]
  have h : exp (-θ * I) * exp (θ * I) = 1 := by rw [← exp_add]; simp
  have hI : I * I = -1 := I_mul_I
  linear_combination (exp (-θ * I) - exp (θ * I)) * exp (θ * I) * hI - h


lemma sin_prod (n : ℕ) (hn : 0 < n) (z : ℂ) :
    ∏ k ∈ range n, sin ((z + k * π) / n) = sin z / 2 ^ (n - 1) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  set ω : ℂ := exp (2 * π * I / n) with hωdef
  have hω : IsPrimitiveRoot ω n := Complex.isPrimitiveRoot_exp n hn.ne'
  set a2 : ℂ := exp (2 * z * I / n) with ha2
  -- each factor
  have hfac : ∀ k : ℕ, exp (2 * ((z + k * π) / n) * I) = ω ^ k * a2 := by
    intro k
    rw [hωdef, ha2, ← exp_nat_mul, ← exp_add]
    congr 1
    field_simp
    ring
  have hP : ∏ k ∈ range n, (exp (2 * ((z + k * π) / n) * I) - 1)
      = (-1) ^ n - (-a2) ^ n := by
    rw [prod_range_sub n hn hω (-1) (-a2)]
    refine Finset.prod_congr rfl (fun k _ => ?_)
    rw [hfac k]; ring
  have ha2n : a2 ^ n = exp (2 * z * I) := by
    rw [ha2, ← exp_nat_mul]; congr 1; field_simp
  have hsum : ∑ k ∈ range n, (z + k * π) / n * I = z * I + (n - 1 : ℕ) * (π / 2 * I) := by
    rw [← Finset.sum_mul, ← Finset.sum_div, Finset.sum_add_distrib, ← Finset.sum_mul]
    simp only [sum_const, card_range, nsmul_eq_mul]
    have h2 : ((∑ i ∈ range n, i : ℕ) : ℂ) * 2 = ((n * (n - 1) : ℕ) : ℂ) := by
      have := Finset.sum_range_id_mul_two n
      exact_mod_cast this
    have : (∑ i ∈ range n, (i : ℂ)) = n * (n - 1 : ℕ) / 2 := by
      push_cast [Nat.cast_mul] at h2 ⊢
      rw [← h2]; ring
    rw [this]
    field_simp
  have hD : ∏ k ∈ range n, (2 * I * exp ((z + k * π) / n * I))
      = (2 * I) ^ n * (exp (z * I) * I ^ (n - 1)) := by
    rw [Finset.prod_mul_distrib, prod_const, card_range, ← exp_sum, hsum, exp_add,
      exp_nat_mul, exp_pi_div_two_mul_I]
  have hmain : (∏ k ∈ range n, sin ((z + k * π) / n)) * ((2 * I) ^ n * (exp (z * I) * I ^ (n - 1)))
      = (-1) ^ n - (-a2) ^ n := by
    rw [← hD, ← Finset.prod_mul_distrib, ← hP]
    refine Finset.prod_congr rfl (fun k _ => ?_)
    rw [sin_mul_eq]
  have hne : (2 * I) ^ n * (exp (z * I) * I ^ (n - 1)) ≠ 0 := by
    apply mul_ne_zero (pow_ne_zero _ (mul_ne_zero two_ne_zero I_ne_zero))
    exact mul_ne_zero (exp_ne_zero _) (pow_ne_zero _ I_ne_zero)
  rw [← eq_div_iff hne] at hmain
  rw [hmain, div_eq_div_iff hne (pow_ne_zero _ two_ne_zero)]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have ha2m : a2 ^ (m + 1) = exp (z * I) * exp (z * I) := by
    rw [ha2n, ← exp_add]; ring_nf
  have h : exp (-z * I) * exp (z * I) = 1 := by rw [← exp_add]; simp
  have hI : I * I = -1 := I_mul_I
  have hJ : I ^ m * I ^ m = (-1) ^ m := by rw [← mul_pow, hI]
  rw [neg_pow a2, ha2m, Complex.sin, mul_pow, pow_succ (-1 : ℂ) m, pow_succ I m, pow_succ (2 : ℂ) m]
  linear_combination (-(exp (-z * I) - exp (z * I)) * exp (z * I) * 2 ^ m * (I ^ m * I ^ m)) * hI
    + ((exp (-z * I) - exp (z * I)) * exp (z * I) * 2 ^ m) * hJ + (2 ^ m * (-1) ^ m) * h

end G15

open Complex Finset
open scoped Real

theorem solution (g : ℕ) (hg : 0 < g) (A : Finset ℕ)
    (hA : A ⊆ Finset.range (2 * g)) (hcard : A.card = g)
    (s : ℂ) (hs : ∀ m : ℤ, s ≠ (m : ℂ)) :
    (Complex.Gamma s
        * ∏ a ∈ A, Complex.sin ((Real.pi : ℂ) * (s + (a : ℂ)) / (2 * (g : ℂ))))
      * (Complex.Gamma (1 - s)
        * ∏ b ∈ Finset.range (2 * g) \ A,
            Complex.sin ((Real.pi : ℂ) * ((1 - s) - (b : ℂ) + 2 * (g : ℂ) - 1) / (2 * (g : ℂ))))
      = (Real.pi : ℂ) / 2 ^ (2 * g - 1) := by
  have hg' : (g : ℂ) ≠ 0 := by exact_mod_cast hg.ne'
  set f : ℕ → ℂ := fun k => Complex.sin ((π * s + k * π) / ((2 * g : ℕ) : ℂ)) with hf
  have hA' : ∀ a : ℕ, Complex.sin ((Real.pi : ℂ) * (s + (a : ℂ)) / (2 * (g : ℂ))) = f a := by
    intro a; rw [hf]; congr 1; push_cast; ring
  have hB' : ∀ b : ℕ, Complex.sin ((Real.pi : ℂ) * ((1 - s) - (b : ℂ) + 2 * (g : ℂ) - 1) / (2 * (g : ℂ)))
      = f b := by
    intro b
    rw [hf, ← Complex.sin_pi_sub]
    congr 1; push_cast; field_simp; ring
  simp_rw [hA', hB']
  have hsin : Complex.sin (π * s) ≠ 0 := by
    rw [Ne, Complex.sin_eq_zero_iff]
    rintro ⟨k, hk⟩
    apply hs k
    have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    apply mul_left_cancel₀ hpi
    rw [hk]; ring
  have hprod : (∏ a ∈ A, f a) * (∏ b ∈ range (2 * g) \ A, f b) = Complex.sin (π * s) / 2 ^ (2 * g - 1) := by
    rw [mul_comm, Finset.prod_sdiff hA, hf]
    exact G15.sin_prod (2 * g) (by omega) (π * s)
  calc Gamma s * (∏ a ∈ A, f a) * (Gamma (1 - s) * ∏ b ∈ range (2 * g) \ A, f b)
      = (Gamma s * Gamma (1 - s)) * ((∏ a ∈ A, f a) * (∏ b ∈ range (2 * g) \ A, f b)) := by ring
    _ = π / 2 ^ (2 * g - 1) := by
      rw [Complex.Gamma_mul_Gamma_one_sub, hprod]
      field_simp
