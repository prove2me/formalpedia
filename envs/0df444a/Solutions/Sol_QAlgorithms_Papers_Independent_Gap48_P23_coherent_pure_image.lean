-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P23.coherent_pure_image
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T00:28:29.880115+00:00
-- url     : https://prove2.me/submissions/1fa09359-ff01-40f4-96e0-f60d97c18101

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P23
noncomputable section

open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P23

open MeasureTheory

open scoped ComplexConjugate Matrix ComplexOrder

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- Exact frozen coordinate helpers; no paper-local redeclarations.

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)


theorem g74g_vand_nat (l j k : ℕ) (hj : j ≤ l) (hk : k ≤ l) :
    (∑ r ∈ Finset.range (l+1), if r + j ≤ l ∧ r + k ≤ l ∧ l ≤ j + k + r then
      (l-j).choose r * j.choose (l-k-r) else 0) = l.choose k := by
  have hV : l.choose k = ∑ r ∈ Finset.range (l-k+1), (l-j).choose r * j.choose (l-k-r) := by
    rw [← Nat.choose_symm hk]
    have := Nat.add_choose_eq (l-j) j (l-k)
    rw [show l - j + j = l by omega] at this
    rw [this, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [hV]
  symm
  rw [← Finset.sum_subset (s₁ := Finset.range (l-k+1)) (s₂ := Finset.range (l+1))]
  · refine Finset.sum_congr rfl fun r hr => ?_
    rw [Finset.mem_range] at hr
    split_ifs with h
    · rfl
    · by_cases h1 : r + j ≤ l
      · have : j < l - k - r := by omega
        rw [Nat.choose_eq_zero_of_lt this, mul_zero]
      · have : l - j < r := by omega
        rw [Nat.choose_eq_zero_of_lt this, zero_mul]
  · intro r; simp only [Finset.mem_range]; omega
  · intro r hr hr'
    simp only [Finset.mem_range] at hr hr'
    rw [if_neg (by omega)]

theorem g74g_vand (l j k : ℕ) (hj : j ≤ l) (hk : k ≤ l) :
    (∑ r ∈ Finset.range (l+1), if r + j ≤ l ∧ r + k ≤ l ∧ l ≤ j + k + r then
      (1:ℂ) / ((Nat.factorial r : ℂ) * Nat.factorial (l - j - r) *
            Nat.factorial (l - k - r) * Nat.factorial (j + k + r - l)) else 0) =
      (Nat.factorial l : ℂ) / ((Nat.factorial j : ℂ) * Nat.factorial (l - j) *
        Nat.factorial k * Nat.factorial (l - k)) := by
  have hterm : ∀ r ∈ Finset.range (l+1), (if r + j ≤ l ∧ r + k ≤ l ∧ l ≤ j + k + r then
      (1:ℂ) / ((Nat.factorial r : ℂ) * Nat.factorial (l - j - r) *
            Nat.factorial (l - k - r) * Nat.factorial (j + k + r - l)) else 0) =
      (((if r + j ≤ l ∧ r + k ≤ l ∧ l ≤ j + k + r then
      (l-j).choose r * j.choose (l-k-r) else 0 : ℕ) : ℂ)) /
        ((Nat.factorial (l-j) : ℂ) * Nat.factorial j) := by
    intro r _
    split_ifs with h
    · have e1 := Nat.choose_mul_factorial_mul_factorial (show r ≤ l - j by omega)
      have e2 := Nat.choose_mul_factorial_mul_factorial (show l - k - r ≤ j by omega)
      rw [show j - (l - k - r) = j + k + r - l by omega] at e2
      rw [show l - j - r = l - j - r from rfl]
      rw [← e1, ← e2]
      push_cast
      have : ((l-j).choose r : ℂ) ≠ 0 := by
        exact_mod_cast (Nat.choose_pos (by omega)).ne'
      have : (j.choose (l-k-r) : ℂ) ≠ 0 := by
        exact_mod_cast (Nat.choose_pos (by omega)).ne'
      field_simp
    · simp
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div, ← Nat.cast_sum, g74g_vand_nat l j k hj hk]
  rw [← Nat.choose_mul_factorial_mul_factorial hk]
  push_cast
  have : ((l.choose k) : ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk).ne'
  field_simp

theorem g74g_sqrt_id (l j k : ℕ) (hj : j ≤ l) (hk : k ≤ l) :
    Real.sqrt ((Nat.factorial j : ℝ) * Nat.factorial (l - j) * Nat.factorial k *
      Nat.factorial (l - k)) * ((Nat.factorial l : ℝ) / ((Nat.factorial j : ℝ) *
        Nat.factorial (l - j) * Nat.factorial k * Nat.factorial (l - k))) =
      Real.sqrt (l.choose j : ℝ) * Real.sqrt (l.choose k : ℝ) := by
  set F : ℝ := (Nat.factorial j : ℝ) * Nat.factorial (l - j) * Nat.factorial k *
      Nat.factorial (l - k) with hFdef
  have hF : 0 < F := by positivity
  rw [← Real.sqrt_mul (by positivity)]
  symm
  rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)]
  have hs : Real.sqrt F * Real.sqrt F = F := Real.mul_self_sqrt hF.le
  rw [Nat.cast_choose ℝ hj, Nat.cast_choose ℝ hk]
  rw [show Real.sqrt F * ((Nat.factorial l : ℝ) / F) * (Real.sqrt F * ((Nat.factorial l : ℝ) / F)) =
      (Real.sqrt F * Real.sqrt F) * ((Nat.factorial l : ℝ) / F) * ((Nat.factorial l : ℝ) / F) by ring,
    hs, hFdef]
  field_simp

theorem g74g_entry (l : ℕ) (psi : EuclideanSpace ℂ (Fin 2)) :
    polynomialIrrep l (pureDensity psi) = pureDensity (monomialKet l psi) := by
  ext j k
  have hj : j.val ≤ l := by omega
  have hk : k.val ≤ l := by omega
  simp only [polynomialIrrep, pureDensity, monomialKet, Matrix.of_apply, PiLp.toLp_apply]
  set a := psi 0
  set b := psi 1
  set P := a^(l - j.val) * b^j.val * (conj a)^(l - k.val) * (conj b)^k.val with hP
  have hterm : ∀ r ∈ Finset.range (l+1),
      (if r + j.val ≤ l ∧ r + k.val ≤ l ∧ l ≤ j.val + k.val + r then
        (a * conj a) ^ r * (a * conj b) ^ (l - j.val - r) * (b * conj a) ^ (l - k.val - r) *
          (b * conj b) ^ (j.val + k.val + r - l) /
          ((Nat.factorial r : ℂ) * Nat.factorial (l - j.val - r) *
            Nat.factorial (l - k.val - r) * Nat.factorial (j.val + k.val + r - l))
      else 0) = P * (if r + j.val ≤ l ∧ r + k.val ≤ l ∧ l ≤ j.val + k.val + r then
      (1:ℂ) / ((Nat.factorial r : ℂ) * Nat.factorial (l - j.val - r) *
            Nat.factorial (l - k.val - r) * Nat.factorial (j.val + k.val + r - l)) else 0) := by
    intro r _
    split_ifs with h
    · set s := l - j.val - r with hs
      set t := l - k.val - r with ht
      set u := j.val + k.val + r - l with hu
      have key : (a * conj a) ^ r * (a * conj b) ^ s * (b * conj a) ^ t * (b * conj b) ^ u = P := by
        rw [hP, show l - j.val = r + s by omega, show l - k.val = r + t by omega,
          show b ^ j.val = b ^ (t + u) from congrArg _ (by omega),
          show (conj b) ^ k.val = (conj b) ^ (s + u) from congrArg _ (by omega)]
        ring
      rw [key, mul_one_div]
    · simp
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, g74g_vand l j.val k.val hj hk]
  have hR := congrArg (fun x : ℝ => (x : ℂ)) (g74g_sqrt_id l j.val k.val hj hk)
  simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_natCast] at hR
  simp only [map_mul, map_pow, Complex.conj_ofReal]
  linear_combination P * hR

theorem g74g_norm (l : ℕ) (psi : EuclideanSpace ℂ (Fin 2)) :
    ‖monomialKet l psi‖^2 = (‖psi‖^2)^l := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_two,
    show ‖psi 0‖^2 + ‖psi 1‖^2 = ‖psi 1‖^2 + ‖psi 0‖^2 from add_comm _ _, add_pow]
  simp only [monomialKet, PiLp.toLp_apply, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [← Fin.sum_univ_eq_sum_range (fun m => (‖psi 1‖ ^ 2) ^ m * (‖psi 0‖ ^ 2) ^ (l - m) * (l.choose m : ℝ))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul]
  ring

/-- PDF p.60, Proposition C.1 and (C.21). PRINTED normalization iff at ell=0
is false at psi=0; CHANGED to exact norm formula for all ell and iff for ell>0.
WHY: the degree-zero vector is [1] for every psi. Independent moderation required. -/
theorem solution (ell : ℕ) (psi : EuclideanSpace ℂ (Fin 2)) :
    polynomialIrrep ell (pureDensity psi) = pureDensity (monomialKet ell psi) ∧
    ‖monomialKet ell psi‖^2 = (‖psi‖^2)^ell ∧
    (0 < ell → (IsState (monomialKet ell psi) ↔ IsState psi)) := by
  refine ⟨g74g_entry ell psi, g74g_norm ell psi, fun hl => ?_⟩
  unfold IsState
  have h := g74g_norm ell psi
  constructor
  · intro hm
    rw [hm, one_pow] at h
    have h2 : ‖psi‖^2 = 1 := (pow_eq_one_iff_of_nonneg (by positivity) hl.ne').mp h.symm
    have := norm_nonneg psi
    nlinarith
  · intro hp
    rw [hp, one_pow, one_pow] at h
    have := norm_nonneg (monomialKet ell psi)
    nlinarith


end
