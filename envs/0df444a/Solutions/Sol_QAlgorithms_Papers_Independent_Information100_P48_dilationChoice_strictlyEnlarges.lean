-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P48.dilationChoice_strictlyEnlarges
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T01:14:43.787792+00:00
-- url     : https://prove2.me/submissions/5d5e6838-b8b2-4678-a4a7-2ce397e1d1c2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P48

namespace QAlgorithms.Papers.Independent.Information100.P48

open scoped Matrix ComplexConjugate ComplexOrder

noncomputable section

theorem g52c_success_gen (Φ : QOp → QOp) (c j : ℝ)
    (hΦ : ∀ X a b, Φ X a b = ((if a then (c : ℂ) else 1) * (if b then (c : ℂ) else 1)) * X a b
      + (if a = false ∧ b = false then (j : ℂ) * X true true else 0)) :
    success Φ = (1 + c ^ 2 + j) / 2 := by
  simp [success, mixedQubit, hΦ, Matrix.trace, Fintype.sum_bool]
  ring

theorem g52c_temporal_gen (Φ : QOp → QOp) (c j : ℝ)
    (hΦ : ∀ X a b, Φ X a b = ((if a then (c : ℂ) else 1) * (if b then (c : ℂ) else 1)) * X a b
      + (if a = false ∧ b = false then (j : ℂ) * X true true else 0))
    (hpos : 0 < 1 + c ^ 2 + j) :
    temporal Φ = 4 * Real.sqrt 2 * c / (1 + c ^ 2 + j) := by
  have hs := g52c_success_gen Φ c j hΦ
  have hne : (1 + c ^ 2 + j) ≠ 0 := hpos.ne'
  simp only [temporal, correlator, conditionalJoint, hs]
  simp [rawJoint, projector, hΦ, pauliX, pauliY, outcomeSign, Matrix.mul_apply, Matrix.trace,
    Fintype.sum_bool]
  field_simp
  ring

theorem g52c_shared_apply (g : ℝ) (hg0 : 0 ≤ g) (X : QOp) (a b : Bool) :
    sharedADC g false X a b =
      ((if a then ((Real.sqrt (1 - g) : ℝ) : ℂ) else 1) * (if b then ((Real.sqrt (1 - g) : ℝ) : ℂ) else 1)) * X a b
      + (if a = false ∧ b = false then ((0 : ℝ) : ℂ) * X true true else 0) := by
  cases a <;> cases b <;>
  simp [sharedADC, branch, cross, selectedOperator, traceEnv, cleanInput, dilation, adcUnitary,
    pairMatrix, pairIndex, outcomeSign, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.single_apply, Matrix.conjTranspose_apply, principalAngle,
    Real.cos_arcsin, ← Complex.ofReal_sin, ← Complex.ofReal_cos, Complex.conj_ofReal, Real.sq_sqrt hg0]
  all_goals ring

theorem g52c_adc_apply (g : ℝ) (hg0 : 0 ≤ g) (X : QOp) (a b : Bool) :
    adc g X a b = ((if a then (Real.sqrt (1 - g) : ℂ) else 1) * (if b then (Real.sqrt (1 - g) : ℂ) else 1)) * X a b
      + (if a = false ∧ b = false then (g : ℂ) * X true true else 0) := by
  have hs : ((Real.sqrt g : ℂ)) * (Real.sqrt g : ℂ) = g := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hg0]
  cases a <;> cases b <;>
    simp [adc, k0, k1, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.conjTranspose_apply]
  all_goals (try rw [← hs]); ring

theorem g52c_temporal_adc (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) :
    temporal (adc g) = 2 * Real.sqrt (2 * (1 - g)) := by
  simp only [temporal, correlator, conditionalJoint, rawJoint, success, projector, mixedQubit]
  simp [g52c_adc_apply g hg0, pauliX, pauliY, outcomeSign, Matrix.mul_apply, Matrix.trace, Fintype.sum_bool]
  have hs2 : Real.sqrt (1 - g) * Real.sqrt (1 - g) = 1 - g := Real.mul_self_sqrt (by linarith)
  rw [hs2]
  have hD : (1 - g) * 2⁻¹ + (2⁻¹ + g * 2⁻¹) = (1:ℝ) := by ring
  rw [hD]
  simp only [div_one]
  ring

theorem g52c_sq_iff (t s g : ℝ) (ht : 0 < t) (ht2 : t ^ 2 = 2) (hs : 0 ≤ s) (hs2 : s ^ 2 = 1 - g)
    (hg0 : 0 ≤ g) (hg1 : g ≤ 1) : (2 - g < 2 * t * s ↔ g < 2 * t - 2) := by
  have h4 : (2 * t * s) ^ 2 = 8 * (1 - g) := by
    have : (2 * t * s) ^ 2 = 4 * (t ^ 2) * (s ^ 2) := by ring
    rw [this, ht2, hs2]; ring
  have hts : 0 ≤ 2 * t * s := by positivity
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    have h1 : 2 * t ≤ g + 2 := by linarith
    have h2 : (2 * t) ^ 2 ≤ (g + 2) ^ 2 := by nlinarith
    have h3 : (2 * t * s) ^ 2 ≤ (2 - g) ^ 2 := by nlinarith
    nlinarith [mul_pos (sub_pos.mpr h) (by linarith : (0:ℝ) < 2 * t * s + (2 - g))]
  · intro h
    have h1 : g + 2 < 2 * t := by linarith
    have h2 : (g + 2) ^ 2 < (2 * t) ^ 2 := by nlinarith
    have h3 : (2 - g) ^ 2 < (2 * t * s) ^ 2 := by nlinarith
    by_contra hc
    push_neg at hc
    nlinarith [mul_le_mul hc hc hts (by linarith : (0:ℝ) ≤ 2 - g)]

theorem g52c_indep_apply (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (X : QOp) (a b : Bool) :
    independentADC g false X a b =
      ((if a then ((Real.sqrt (1 - g) : ℝ) : ℂ) else 1) * (if b then ((Real.sqrt (1 - g) : ℝ) : ℂ) else 1)) * X a b
      + (if a = false ∧ b = false then ((g / 2 : ℝ) : ℂ) * X true true else 0) := by
  have hs1 : Real.sqrt g ≤ 1 := by rw [Real.sqrt_le_one]; exact hg1
  have hs0 : -1 ≤ Real.sqrt g := by linarith [Real.sqrt_nonneg g]
  have hsin : Real.sin (Real.arcsin (Real.sqrt g)) = Real.sqrt g := Real.sin_arcsin hs0 hs1
  have hc : ((Real.sqrt g : ℝ) : ℂ) ^ 2 = (g : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hg0]
  cases a <;> cases b <;>
  simp [independentADC, branch, cross, selectedOperator, traceEnv, cleanInput, embed0, embed1,
    dilation, adcUnitary,
    pairMatrix, pairIndex, outcomeSign, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.single_apply, Matrix.conjTranspose_apply, principalAngle,
    Real.cos_arcsin, ← Complex.ofReal_sin, ← Complex.ofReal_cos, Complex.conj_ofReal, Real.sq_sqrt hg0,
    hsin, hc]
  all_goals first | ring1 | linear_combination (X true true * (1/2)) * hc |
    linear_combination (X true true) * hc | linear_combination (X true true * (1/2 : ℂ)) * hc

theorem g52c_sq_iff2 (t u s g : ℝ) (ht : 0 < t) (ht2 : t ^ 2 = 2) (hu : 0 < u) (hu2 : u ^ 2 = 10)
    (hs : 0 ≤ s) (hs2 : s ^ 2 = 1 - g)
    (hg0 : 0 ≤ g) (hg1 : g ≤ 1) : (4 - g < 4 * t * s ↔ g < 4 * u - 12) := by
  have h4 : (4 * t * s) ^ 2 = 32 * (1 - g) := by
    have : (4 * t * s) ^ 2 = 16 * (t ^ 2) * (s ^ 2) := by ring
    rw [this, ht2, hs2]; ring
  have h5 : (4 * u) ^ 2 = 160 := by
    have : (4 * u) ^ 2 = 16 * u ^ 2 := by ring
    rw [this, hu2]; norm_num
  have hts : 0 ≤ 4 * t * s := by positivity
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    have h1 : 4 * u ≤ g + 12 := by linarith
    have h2 : (4 * u) ^ 2 ≤ (g + 12) ^ 2 := by nlinarith
    have h3 : (4 * t * s) ^ 2 ≤ (4 - g) ^ 2 := by nlinarith
    nlinarith [mul_pos (sub_pos.mpr h) (by linarith : (0:ℝ) < 4 * t * s + (4 - g))]
  · intro h
    have h1 : g + 12 < 4 * u := by linarith
    have h2 : (g + 12) ^ 2 < (4 * u) ^ 2 := by nlinarith
    have h3 : (4 - g) ^ 2 < (4 * t * s) ^ 2 := by nlinarith
    by_contra hc
    push_neg at hc
    nlinarith [mul_le_mul hc hc hts (by linarith : (0:ℝ) ≤ 4 - g)]


theorem g52c_adc_le_two (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) : temporal (adc g) ≤ 2 ↔ 1 / 2 ≤ g := by
  rw [g52c_temporal_adc g hg0 hg1]
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    have : Real.sqrt 1 < Real.sqrt (2 * (1 - g)) := Real.sqrt_lt_sqrt (by norm_num) (by linarith)
    rw [Real.sqrt_one] at this
    linarith
  · intro h
    have : Real.sqrt (2 * (1 - g)) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (by linarith)
    rw [Real.sqrt_one] at this
    linarith

theorem g52c_crit_bounds : (1 / 2 : ℝ) ≤ independentCritical ∧ independentCritical < sharedCritical ∧
    sharedCritical < 1 := by
  simp only [independentCritical, sharedCritical]
  have h10 : Real.sqrt 10 < 3.163 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  have h10' : (3.162 : ℝ) < Real.sqrt 10 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have h2 : (1.414 : ℝ) < Real.sqrt 2 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have h2' : Real.sqrt 2 < 1.415 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  refine ⟨by linarith, by linarith, by linarith⟩

theorem g52c_shared_iff (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) :
    2 < temporal (sharedADC g false) ↔ g < sharedCritical := by
  have hS := g52c_shared_apply g hg0
  have hsq : (Real.sqrt (1 - g)) ^ 2 = 1 - g := Real.sq_sqrt (by linarith)
  have hpos : 0 < 1 + (Real.sqrt (1 - g)) ^ 2 + 0 := by positivity
  have h2g : 0 < 2 - g := by linarith
  have ht : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have ht2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt (1 - g) := Real.sqrt_nonneg _
  rw [g52c_temporal_gen _ _ _ hS hpos, hsq, show (1:ℝ) + (1 - g) + 0 = 2 - g by ring,
    lt_div_iff₀ h2g, sharedCritical]
  have := g52c_sq_iff (Real.sqrt 2) (Real.sqrt (1 - g)) g ht ht2 hs0 hsq hg0 hg1
  constructor
  · intro h; have := this.mp (by nlinarith); linarith
  · intro h; have := this.mpr (by linarith); nlinarith

theorem g52c_indep_iff (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) :
    2 < temporal (independentADC g false) ↔ g < independentCritical := by
  have hS := g52c_indep_apply g hg0 hg1
  have hsq : (Real.sqrt (1 - g)) ^ 2 = 1 - g := Real.sq_sqrt (by linarith)
  have hpos : 0 < 1 + (Real.sqrt (1 - g)) ^ 2 + g / 2 := by positivity
  have h4g : 0 < 4 - g := by linarith
  have ht : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have ht2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hu : 0 < Real.sqrt 10 := Real.sqrt_pos.mpr (by norm_num)
  have hu2 : (Real.sqrt 10) ^ 2 = 10 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt (1 - g) := Real.sqrt_nonneg _
  rw [g52c_temporal_gen _ _ _ hS hpos, hsq, show (1:ℝ) + (1 - g) + g / 2 = (4 - g) / 2 by ring,
    lt_div_iff₀ (by linarith), independentCritical]
  have := g52c_sq_iff2 (Real.sqrt 2) (Real.sqrt 10) (Real.sqrt (1 - g)) g ht ht2 hu hu2 hs0 hsq hg0 hg1
  constructor
  · intro h; have := this.mp (by nlinarith); linarith
  · intro h; have := this.mpr (by linarith); nlinarith

theorem g52c_shared_true_apply (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (X : QOp) (a b : Bool) :
    sharedADC g true X a b = if a = false ∧ b = false then (g : ℂ) * X true true else 0 := by
  have hs1 : Real.sqrt g ≤ 1 := by rw [Real.sqrt_le_one]; exact hg1
  have hs0 : -1 ≤ Real.sqrt g := by linarith [Real.sqrt_nonneg g]
  have hsin : Real.sin (Real.arcsin (Real.sqrt g)) = Real.sqrt g := Real.sin_arcsin hs0 hs1
  have hc : ((Real.sqrt g : ℝ) : ℂ) ^ 2 = (g : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hg0]
  cases a <;> cases b <;>
  simp [sharedADC, branch, cross, selectedOperator, traceEnv, cleanInput, dilation, adcUnitary,
    pairMatrix, pairIndex, outcomeSign, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.single_apply, Matrix.conjTranspose_apply, principalAngle,
    Real.cos_arcsin, ← Complex.ofReal_sin, ← Complex.ofReal_cos, Complex.conj_ofReal, Real.sq_sqrt hg0,
    hsin, hc]
  all_goals first | ring1 | linear_combination (X true true * (1/2)) * hc |
    linear_combination (X true true) * hc | linear_combination (X true true * (1/2 : ℂ)) * hc

theorem g52c_indep_true_apply (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (X : QOp) (a b : Bool) :
    independentADC g true X a b = if a = false ∧ b = false then ((g / 2 : ℝ) : ℂ) * X true true else 0 := by
  have hs1 : Real.sqrt g ≤ 1 := by rw [Real.sqrt_le_one]; exact hg1
  have hs0 : -1 ≤ Real.sqrt g := by linarith [Real.sqrt_nonneg g]
  have hsin : Real.sin (Real.arcsin (Real.sqrt g)) = Real.sqrt g := Real.sin_arcsin hs0 hs1
  have hc : ((Real.sqrt g : ℝ) : ℂ) ^ 2 = (g : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hg0]
  cases a <;> cases b <;>
  simp [independentADC, branch, cross, selectedOperator, traceEnv, cleanInput, embed0, embed1,
    dilation, adcUnitary,
    pairMatrix, pairIndex, outcomeSign, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.single_apply, Matrix.conjTranspose_apply, principalAngle,
    Real.cos_arcsin, ← Complex.ofReal_sin, ← Complex.ofReal_cos, Complex.conj_ofReal, Real.sq_sqrt hg0,
    hsin, hc]
  all_goals first | ring1 | linear_combination (X true true * (1/2)) * hc |
    linear_combination (X true true) * hc | linear_combination (X true true * (1/2 : ℂ)) * hc

end

end QAlgorithms.Papers.Independent.Information100.P48

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Information100 QAlgorithms.Papers.Independent.Information100.P48 in
open scoped Matrix ComplexConjugate ComplexOrder in
theorem solution :
    activation (fun g => independentADC g false) = Set.Ico (1 / 2) independentCritical ∧
    activation (fun g => sharedADC g false) = Set.Ico (1 / 2) sharedCritical ∧
    activation (fun g => independentADC g false) ⊂
      activation (fun g => sharedADC g false) ∧
    (∀ g : ℝ, 0 ≤ g → g ≤ 1 → ∀ rho : QOp,
      independentADC g false rho + independentADC g true rho = adc g rho ∧
      sharedADC g false rho + sharedADC g true rho = adc g rho) ∧
    (∃ rho : QOp, IsDensityMatrix rho ∧
      normalize (independentADC (1 / 2) false rho) ≠
        normalize (sharedADC (1 / 2) false rho)) := by
  obtain ⟨hc1, hc2, hc3⟩ := g52c_crit_bounds
  have hA : activation (fun g => independentADC g false) = Set.Ico (1 / 2) independentCritical := by
    ext g
    simp only [activation, Set.mem_setOf_eq, Set.mem_Ico]
    constructor
    · rintro ⟨hg0, hg1, h1, h2⟩
      exact ⟨(g52c_adc_le_two g hg0 hg1).mp h1, (g52c_indep_iff g hg0 hg1).mp h2⟩
    · rintro ⟨h1, h2⟩
      have hg0 : 0 ≤ g := by linarith
      have hg1 : g ≤ 1 := by linarith
      exact ⟨hg0, hg1, (g52c_adc_le_two g hg0 hg1).mpr h1, (g52c_indep_iff g hg0 hg1).mpr h2⟩
  have hB : activation (fun g => sharedADC g false) = Set.Ico (1 / 2) sharedCritical := by
    ext g
    simp only [activation, Set.mem_setOf_eq, Set.mem_Ico]
    constructor
    · rintro ⟨hg0, hg1, h1, h2⟩
      exact ⟨(g52c_adc_le_two g hg0 hg1).mp h1, (g52c_shared_iff g hg0 hg1).mp h2⟩
    · rintro ⟨h1, h2⟩
      have hg0 : 0 ≤ g := by linarith
      have hg1 : g ≤ 1 := by linarith
      exact ⟨hg0, hg1, (g52c_adc_le_two g hg0 hg1).mpr h1, (g52c_shared_iff g hg0 hg1).mpr h2⟩
  refine ⟨hA, hB, ?_, ?_, ?_⟩
  · rw [hA, hB]
    refine ⟨Set.Ico_subset_Ico_right hc2.le, fun h => ?_⟩
    have : independentCritical ∈ Set.Ico (1 / 2) sharedCritical := ⟨hc1, hc2⟩
    exact (h this).2.false
  · intro g hg0 hg1 rho
    constructor
    · ext a b
      rw [Matrix.add_apply, g52c_indep_apply g hg0 hg1, g52c_indep_true_apply g hg0 hg1,
        g52c_adc_apply g hg0]
      split_ifs <;> push_cast <;> ring
    · ext a b
      rw [Matrix.add_apply, g52c_shared_apply g hg0, g52c_shared_true_apply g hg0 hg1,
        g52c_adc_apply g hg0]
      split_ifs <;> push_cast <;> ring
  · refine ⟨Matrix.diagonal (fun b => if b then 1 else 0), ⟨?_, ?_⟩, ?_⟩
    · apply Matrix.PosSemidef.diagonal
      intro b; cases b <;> simp
    · simp [Matrix.trace, Fintype.sum_bool]
    · intro h
      have := congrFun (congrFun h false) false
      simp only [QAlgorithms.Papers.Independent.Information100.P48.normalize, Matrix.smul_apply, smul_eq_mul, Matrix.trace, Matrix.diag,
        Fintype.sum_bool] at this
      simp only [g52c_indep_apply (1/2) (by norm_num) (by norm_num),
        g52c_shared_apply (1/2) (by norm_num), Matrix.diagonal_apply] at this
      norm_num at this
      have h2 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; push_cast; ring
      have h3 : (3 / 4 : ℂ) = 0 := by linear_combination this - (1 / 4 : ℂ) * h2
      norm_num at h3
