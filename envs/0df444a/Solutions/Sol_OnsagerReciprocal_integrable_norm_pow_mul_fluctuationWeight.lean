-- Prove2me | solution 1 for OnsagerReciprocal.integrable_norm_pow_mul_fluctuationWeight
-- status  : ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-10T23:34:31.280985+00:00
-- url     : https://prove2.me/submissions/01385c9d-6896-47c0-896d-b7851932c9c2

import Mathlib
import Definitions.Def_OnsagerReciprocal_basic

open Matrix MeasureTheory

set_option autoImplicit false

/-!
# Polynomial moments of the Gaussian fluctuation weight are finite

For positive definite `β`, `x ↦ ‖x‖ ^ m * fluctuationWeight β x` is Lebesgue integrable.
Proof: coercivity `c ‖x‖² ≤ xᵀβx` (minimum of the quadratic form on the compact unit sphere),
hence `w(x) ≤ exp (-(c/2)‖x‖²)`; then `‖x‖^m exp(-(c/2)‖x‖²) ≤ C (1 + ‖x‖)^{-(n+1)}`, which is
integrable by `integrable_one_add_norm`.
-/

private lemma quad_smul {n : ℕ} (β : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) (y : Fin n → ℝ) :
    (t • y) ⬝ᵥ (β *ᵥ (t • y)) = t ^ 2 * (y ⬝ᵥ (β *ᵥ y)) := by
  rw [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  ring

private lemma coercive {n : ℕ} (β : Matrix (Fin n) (Fin n) ℝ) (hβ : β.PosDef) :
    ∃ c > 0, ∀ x : Fin n → ℝ, c * ‖x‖ ^ 2 ≤ x ⬝ᵥ (β *ᵥ x) := by
  rcases isEmpty_or_nonempty (Fin n) with h | h
  · refine ⟨1, one_pos, fun x => ?_⟩
    have : x = 0 := Subsingleton.elim _ _
    subst this
    simp
  · have hS : IsCompact (Metric.sphere (0 : Fin n → ℝ) 1) := isCompact_sphere 0 1
    have hne : (Metric.sphere (0 : Fin n → ℝ) 1).Nonempty :=
      NormedSpace.sphere_nonempty.mpr zero_le_one
    have hcont : Continuous fun x : Fin n → ℝ => x ⬝ᵥ (β *ᵥ x) := by
      fun_prop
    obtain ⟨u, hu, hmin⟩ := hS.exists_isMinOn hne hcont.continuousOn
    refine ⟨u ⬝ᵥ (β *ᵥ u), ?_, fun x => ?_⟩
    · have hu0 : u ≠ 0 := by
        rintro rfl
        simp at hu
      simpa using hβ.dotProduct_mulVec_pos hu0
    · by_cases hx : x = 0
      · subst hx
        simp
      · have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx
        have hy : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : Fin n → ℝ) 1 := by
          simp [norm_smul, hxn.ne']
        have h1 : u ⬝ᵥ (β *ᵥ u) ≤ (‖x‖⁻¹ • x) ⬝ᵥ (β *ᵥ (‖x‖⁻¹ • x)) := hmin hy
        have hxy : ‖x‖ • (‖x‖⁻¹ • x) = x := by
          rw [smul_smul, mul_inv_cancel₀ hxn.ne', one_smul]
        calc u ⬝ᵥ (β *ᵥ u) * ‖x‖ ^ 2
            ≤ ‖x‖ ^ 2 * ((‖x‖⁻¹ • x) ⬝ᵥ (β *ᵥ (‖x‖⁻¹ • x))) := by
              rw [mul_comm]
              exact mul_le_mul_of_nonneg_left h1 (by positivity)
          _ = x ⬝ᵥ (β *ᵥ x) := by
              rw [← quad_smul β ‖x‖ (‖x‖⁻¹ • x), hxy]

/-- Scalar bound: `r ^ m * exp (-a r²) * (1 + r) ^ (n+1) ≤ C`. -/
private lemma scalar_bound (a : ℝ) (ha : 0 < a) (m k : ℕ) :
    ∃ C, ∀ r : ℝ, 0 ≤ r → r ^ m * Real.exp (-a * r ^ 2) * (1 + r) ^ k ≤ C := by
  set N : ℕ := m + k + 1 with hN
  have hNpos : (0 : ℝ) < N := by positivity
  set b : ℝ := a / N with hb
  have hbpos : 0 < b := div_pos ha hNpos
  refine ⟨(2 * (1 + 1 / b)) ^ N, fun r hr => ?_⟩
  have h1r : (1 : ℝ) ≤ 1 + r := by linarith
  have hrm : r ^ m ≤ (1 + r) ^ m := pow_le_pow_left₀ hr (by linarith) m
  have hstep1 : r ^ m * (1 + r) ^ k ≤ (1 + r) ^ N := by
    calc r ^ m * (1 + r) ^ k ≤ (1 + r) ^ m * (1 + r) ^ k :=
          mul_le_mul_of_nonneg_right hrm (by positivity)
      _ = (1 + r) ^ (m + k) := by rw [pow_add]
      _ ≤ (1 + r) ^ N := pow_le_pow_right₀ h1r (by omega)
  have hstep2 : (1 + r) ^ N ≤ ((1 + r) ^ 2) ^ N := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ h1r (by omega)
  have hsq : (1 + r) ^ 2 ≤ 2 * (1 + 1 / b) * (1 + b * r ^ 2) := by
    have e1 : (1 + r) ^ 2 ≤ 2 * (1 + r ^ 2) := by nlinarith [sq_nonneg (1 - r)]
    have e2 : 1 + r ^ 2 ≤ (1 + 1 / b) * (1 + b * r ^ 2) := by
      have : (1 + 1 / b) * (1 + b * r ^ 2) = 1 + r ^ 2 + (1 / b + b * r ^ 2) := by
        field_simp
        ring
      rw [this]
      have : 0 ≤ 1 / b + b * r ^ 2 := by positivity
      linarith
    nlinarith
  have hstep3 : ((1 + r) ^ 2) ^ N ≤ (2 * (1 + 1 / b)) ^ N * (1 + b * r ^ 2) ^ N := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith) N
  have hexp : (1 + b * r ^ 2) ^ N ≤ Real.exp (a * r ^ 2) := by
    have h0 : 1 + b * r ^ 2 ≤ Real.exp (b * r ^ 2) := by
      have := Real.add_one_le_exp (b * r ^ 2); linarith
    calc (1 + b * r ^ 2) ^ N ≤ Real.exp (b * r ^ 2) ^ N :=
          pow_le_pow_left₀ (by positivity) h0 N
      _ = Real.exp (N * (b * r ^ 2)) := (Real.exp_nat_mul _ _).symm
      _ = Real.exp (a * r ^ 2) := by
          congr 1
          rw [hb]
          field_simp
  have hE : Real.exp (-a * r ^ 2) * Real.exp (a * r ^ 2) = 1 := by
    rw [← Real.exp_add]; simp
  have hEpos : 0 < Real.exp (-a * r ^ 2) := Real.exp_pos _
  calc r ^ m * Real.exp (-a * r ^ 2) * (1 + r) ^ k
      = Real.exp (-a * r ^ 2) * (r ^ m * (1 + r) ^ k) := by ring
    _ ≤ Real.exp (-a * r ^ 2) * ((2 * (1 + 1 / b)) ^ N * Real.exp (a * r ^ 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ hEpos.le
        calc r ^ m * (1 + r) ^ k ≤ ((1 + r) ^ 2) ^ N := hstep1.trans hstep2
          _ ≤ (2 * (1 + 1 / b)) ^ N * (1 + b * r ^ 2) ^ N := hstep3
          _ ≤ (2 * (1 + 1 / b)) ^ N * Real.exp (a * r ^ 2) :=
              mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = (2 * (1 + 1 / b)) ^ N := by
        rw [mul_left_comm, hE, mul_one]

private lemma continuous_fluctuationWeight {n : ℕ} (β : Matrix (Fin n) (Fin n) ℝ) :
    Continuous (OnsagerReciprocal.fluctuationWeight β) := by
  unfold OnsagerReciprocal.fluctuationWeight
  fun_prop

theorem solution {n : ℕ} (β : Matrix (Fin n) (Fin n) ℝ)
    (hβ : β.PosDef) (m : ℕ) :
    MeasureTheory.Integrable
      (fun x : Fin n → ℝ => ‖x‖ ^ m * OnsagerReciprocal.fluctuationWeight β x) := by
  obtain ⟨c, hc, hcoer⟩ := coercive β hβ
  obtain ⟨C, hC⟩ := scalar_bound (c / 2) (by positivity) m (n + 1)
  have hint : Integrable (fun x : Fin n → ℝ => C * (1 + ‖x‖) ^ (-(((n + 1 : ℕ) : ℝ)))) := by
    refine (integrable_one_add_norm ?_).const_mul C
    rw [Module.finrank_fin_fun]
    norm_cast
    omega
  refine hint.mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact (by fun_prop : Continuous fun x : Fin n → ℝ => ‖x‖ ^ m).mul
      (continuous_fluctuationWeight β) |>.aestronglyMeasurable
  · have hw : OnsagerReciprocal.fluctuationWeight β x ≤ Real.exp (-(c / 2) * ‖x‖ ^ 2) := by
      unfold OnsagerReciprocal.fluctuationWeight
      apply Real.exp_le_exp.mpr
      have := hcoer x
      linarith
    have hwpos : 0 < OnsagerReciprocal.fluctuationWeight β x := Real.exp_pos _
    have h1 : 0 < 1 + ‖x‖ := by positivity
    rw [Real.norm_of_nonneg (by positivity), Real.rpow_neg h1.le, Real.rpow_natCast]
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    calc ‖x‖ ^ m * OnsagerReciprocal.fluctuationWeight β x * (1 + ‖x‖) ^ (n + 1)
        ≤ ‖x‖ ^ m * Real.exp (-(c / 2) * ‖x‖ ^ 2) * (1 + ‖x‖) ^ (n + 1) := by
          gcongr
      _ ≤ C := hC ‖x‖ (norm_nonneg x)
