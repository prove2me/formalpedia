-- Prove2me | solution 1 for UnderstandingML.linear_regression_not_learnable
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-25T16:44:21.954801+00:00
-- url     : https://prove2.me/submissions/cee72164-b813-4c00-a003-0b8f0b54e43d

import Definitions.Def_UnderstandingML_Convex

open MeasureTheory
open scoped InnerProductSpace
open UnderstandingML

namespace LinRegNotLearnable

/-- Integral of a function against `a • δ_x + b • δ_y`. -/
lemma integral_two_point (f : ℝ × ℝ → ℝ) (x y : ℝ × ℝ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∫ z, f z ∂(ENNReal.ofReal a • Measure.dirac x + ENNReal.ofReal b • Measure.dirac y) =
      a * f x + b * f y := by
  rw [integral_add_measure, integral_smul_measure, integral_smul_measure, integral_dirac,
    integral_dirac, ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal hb, smul_eq_mul, smul_eq_mul]
  · exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  · exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

lemma risk_two_point (w : ℝ) (x y : ℝ × ℝ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    risk squaredLoss1
        (ENNReal.ofReal a • Measure.dirac x + ENNReal.ofReal b • Measure.dirac y) w =
      a * squaredLoss1 w x + b * squaredLoss1 w y :=
  integral_two_point _ x y a b ha hb

lemma risk_dirac (w : ℝ) (y : ℝ × ℝ) :
    risk squaredLoss1 (Measure.dirac y) w = squaredLoss1 w y := by
  unfold risk; rw [integral_dirac]

/-- The sample of `m` copies of `z` has `D^m`-probability at least `D{z}^m`, and any set
containing it has at least this outer measure. -/
lemma iidLaw_ge_of_const {D : Measure (ℝ × ℝ)} [IsProbabilityMeasure D] (m : ℕ) (z : ℝ × ℝ)
    (s : Set (Fin m → ℝ × ℝ)) (hs : (fun _ ↦ z) ∈ s) :
    D {z} ^ m ≤ iidLaw D m s := by
  have hsub : Set.univ.pi (fun _ : Fin m ↦ ({z} : Set (ℝ × ℝ))) ⊆ s := by
    intro S hS
    have : S = fun _ ↦ z := funext fun i ↦ by simpa using hS i (Set.mem_univ i)
    rw [this]; exact hs
  calc D {z} ^ m = ∏ _i : Fin m, D {z} := by simp
    _ = iidLaw D m (Set.univ.pi fun _ : Fin m ↦ ({z} : Set (ℝ × ℝ))) := by
        unfold iidLaw; rw [Measure.pi_pi]
    _ ≤ iidLaw D m s := measure_mono hsub

/-- The core argument (Examples 12.8–12.9): any class `H ⊆ ℝ` containing `-1` and `0` is not
agnostic PAC learnable for linear regression with the squared loss. -/
theorem not_learnable_of_mem (H : Set ℝ) (h1 : (-1 : ℝ) ∈ H) (h0 : (0 : ℝ) ∈ H) :
    ¬ AgnosticPACLearnable squaredLoss1 H := by
  rintro ⟨mH, A, -, hA⟩
  set ε : ℝ := 1 / 100
  set δ : ℝ := 1 / 2
  set m : ℕ := mH ε δ
  set c : ℝ := 8 * (m + 1) with hc
  have hc1 : 8 ≤ c := by rw [hc]; have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith
  set μ : ℝ := 1 / c with hμ
  have hμ0 : 0 < μ := by rw [hμ]; positivity
  have hμc : μ * c = 1 := by rw [hμ]; field_simp
  have hμ1 : μ ≤ 1 / 8 := by rw [hμ]; exact one_div_le_one_div_of_le (by norm_num) hc1
  set z1 : ℝ × ℝ := (c, 0)
  set z2 : ℝ × ℝ := (1, -1)
  set S0 : Fin m → ℝ × ℝ := fun _ ↦ z2
  set wh : ℝ := A m S0
  by_cases hw : wh ≤ -1 / 2
  · -- the two-point distribution `D₁`
    set D1 : Measure (ℝ × ℝ) :=
      ENNReal.ofReal μ • Measure.dirac z1 + ENNReal.ofReal (1 - μ) • Measure.dirac z2
    have hD1 : IsProbabilityMeasure D1 := by
      constructor
      simp only [D1, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
      rw [← ENNReal.ofReal_add hμ0.le (by linarith)]
      simp
    have hrisk : ∀ w, risk squaredLoss1 D1 w = μ * (w * c) ^ 2 + (1 - μ) * (w + 1) ^ 2 := by
      intro w
      rw [risk_two_point w z1 z2 μ (1 - μ) hμ0.le (by linarith)]
      simp only [squaredLoss1, z1, z2]; ring
    have hbad : ∃ h' ∈ H, risk squaredLoss1 D1 h' + ε < risk squaredLoss1 D1 (A m S0) := by
      refine ⟨0, h0, ?_⟩
      rw [hrisk, hrisk]
      have h2 : μ * (wh * c) ^ 2 ≥ 2 := by
        have : (wh * c) ^ 2 ≥ (c / 2) ^ 2 := by
          have : wh * c ≤ -(c / 2) := by nlinarith
          nlinarith
        have e : μ * (c / 2) ^ 2 = c / 4 := by rw [div_pow, ← mul_div_assoc, sq, ← mul_assoc, hμc]; ring
        nlinarith
      have : 0 ≤ (1 - μ) * (wh + 1) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
      simp only [wh] at h2 this
      norm_num [ε]
      nlinarith
    have hmeas := hA ε δ (by norm_num [ε]) (by norm_num [ε]) (by norm_num [δ]) (by norm_num [δ])
      D1 hD1 m le_rfl
    have hge := iidLaw_ge_of_const (D := D1) m z2
      {S | ∃ h' ∈ H, risk squaredLoss1 D1 h' + ε < risk squaredLoss1 D1 (A m S)} hbad
    have hz2 : ENNReal.ofReal (1 - μ) ≤ D1 {z2} := by
      simp only [D1, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
      simp
    have hpow : ENNReal.ofReal ((1 - μ) ^ m) ≤ D1 {z2} ^ m := by
      rw [ENNReal.ofReal_pow (by linarith)]
      exact pow_le_pow_left₀ (by positivity) hz2 m
    have hbern : (1 : ℝ) / 2 < (1 - μ) ^ m := by
      have := one_add_mul_le_pow (a := -μ) (by linarith) m
      have hmμ : (m : ℝ) * μ ≤ 1 / 8 := by
        rw [hμ, hc]
        rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
        linarith
      have e : (1 : ℝ) + -μ = 1 - μ := by ring
      rw [e] at this
      nlinarith
    have := (hpow.trans hge).trans hmeas
    rw [ENNReal.ofReal_le_ofReal_iff (by norm_num [δ])] at this
    simp only [δ] at this
    linarith
  · -- the point mass `D₂ = δ_{z₂}`
    replace hw := lt_of_not_ge hw
    set D2 : Measure (ℝ × ℝ) := Measure.dirac z2
    have hbad : ∃ h' ∈ H, risk squaredLoss1 D2 h' + ε < risk squaredLoss1 D2 (A m S0) := by
      refine ⟨-1, h1, ?_⟩
      rw [risk_dirac, risk_dirac]
      simp only [squaredLoss1, z2, ε]
      have : (1 : ℝ) / 2 < wh + 1 := by linarith
      simp only [wh] at this
      nlinarith
    have hmeas := hA ε δ (by norm_num [ε]) (by norm_num [ε]) (by norm_num [δ]) (by norm_num [δ])
      D2 inferInstance m le_rfl
    have hge := iidLaw_ge_of_const (D := D2) m z2
      {S | ∃ h' ∈ H, risk squaredLoss1 D2 h' + ε < risk squaredLoss1 D2 (A m S)} hbad
    simp only [D2, Measure.dirac_apply_of_mem (Set.mem_singleton z2), one_pow] at hge
    have := hge.trans hmeas
    rw [← ENNReal.ofReal_one, ENNReal.ofReal_le_ofReal_iff (by norm_num [δ])] at this
    norm_num [δ] at this

end LinRegNotLearnable

theorem solution :
    ¬ AgnosticPACLearnable squaredLoss1 (Set.univ : Set ℝ) ∧
    ¬ AgnosticPACLearnable squaredLoss1 (Set.Icc (-1 : ℝ) 1) :=
  ⟨LinRegNotLearnable.not_learnable_of_mem _ (Set.mem_univ _) (Set.mem_univ _),
    LinRegNotLearnable.not_learnable_of_mem _ (by norm_num) (by norm_num)⟩
