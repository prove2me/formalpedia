-- Prove2me | solution 1 for PhaseEncodedQGE.lemma_A_20
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-17T10:23:37.502492+00:00
-- url     : https://prove2.me/submissions/e8e9eeb1-0b5a-467c-914a-2f5ebbd08171

import Mathlib
import Theorems.Thm_DiazModulus_hermite_lindemann_holds
import Definitions.Def_PhaseEncodedQGE_Profile


set_option autoImplicit false

namespace PhaseEncodedQGE.Schedule

theorem algebraic_I : IsAlgebraic ℚ Complex.I := by
  apply IsAlgebraic.of_pow (n := 2) (by decide)
  simpa using (isAlgebraic_one (R := ℚ) (A := ℂ)).neg

theorem cos_transcendental_of_HL
    (hl : ∀ a : ℂ, a ≠ 0 → IsAlgebraic ℚ a → Transcendental ℚ (Complex.exp a))
    {η : ℝ} (hη : η ≠ 0) (ha : IsAlgebraic ℚ η) :
    Transcendental ℚ (Real.cos η) := by
  intro hc
  have hs : IsAlgebraic ℚ (Real.sin η) := by
    apply IsAlgebraic.of_pow (n := 2) (by decide)
    have h := (isAlgebraic_one (R := ℚ) (A := ℝ)).sub (hc.pow 2)
    have heq : Real.sin η ^ 2 = 1 - Real.cos η ^ 2 := by nlinarith [Real.sin_sq_add_cos_sq η]
    rwa [← heq] at h
  have he : IsAlgebraic ℚ (Complex.exp ((η : ℂ) * Complex.I)) := by
    rw [Complex.exp_mul_I]
    have hcC : IsAlgebraic ℚ ((Real.cos η : ℝ) : ℂ) := hc.algebraMap
    have hsC : IsAlgebraic ℚ ((Real.sin η : ℝ) : ℂ) := hs.algebraMap
    simpa only [← Complex.ofReal_cos, ← Complex.ofReal_sin] using
      hcC.add (hsC.mul algebraic_I)
  have hn : (η : ℂ) * Complex.I ≠ 0 := mul_ne_zero (by exact_mod_cast hη) Complex.I_ne_zero
  exact hl _ hn (ha.algebraMap.mul algebraic_I) he

theorem tan_sq_half_transcendental_of_HL
    (hl : ∀ a : ℂ, a ≠ 0 → IsAlgebraic ℚ a → Transcendental ℚ (Complex.exp a))
    {η : ℝ} (hη : η ≠ 0) (ha : IsAlgebraic ℚ η) (hc : Real.cos η ≠ -1) :
    Transcendental ℚ (Real.tan (η / 2) ^ 2) := by
  intro ht
  apply cos_transcendental_of_HL hl hη ha
  rw [Real.cos_eq_two_mul_tan_half_div_one_sub_tan_half_sq η hc]
  rw [div_eq_mul_inv]
  exact ((isAlgebraic_one (R := ℚ)).sub ht).mul ((isAlgebraic_one (R := ℚ)).add ht).inv


theorem cos_transcendental {η : ℝ} (hη : η ≠ 0) (ha : IsAlgebraic ℚ η) :
    Transcendental ℚ (Real.cos η) :=
  cos_transcendental_of_HL DiazModulus.hermite_lindemann_holds hη ha

theorem tan_sq_half_transcendental {η : ℝ} (hη : η ≠ 0)
    (ha : IsAlgebraic ℚ η) (hc : Real.cos η ≠ -1) :
    Transcendental ℚ (Real.tan (η / 2) ^ 2) :=
  tan_sq_half_transcendental_of_HL DiazModulus.hermite_lindemann_holds hη ha hc

theorem cos_schedule_transcendental : Transcendental ℚ (Real.cos (23 / 8 : ℝ)) := by
  apply cos_transcendental (by norm_num)
  rw [div_eq_mul_inv]
  exact (isAlgebraic_natCast (R := ℚ) (A := ℝ) 23).mul
    (isAlgebraic_natCast (R := ℚ) (A := ℝ) 8).inv

theorem tan_sq_schedule_transcendental : Transcendental ℚ (Real.tan (23 / 16 : ℝ) ^ 2) := by
  have hc : Real.cos (23 / 8 : ℝ) ≠ -1 := by
    intro h
    exact cos_schedule_transcendental (h ▸ (isAlgebraic_one (R := ℚ) (A := ℝ)).neg)
  have ha : IsAlgebraic ℚ (23 / 8 : ℝ) := by
    rw [div_eq_mul_inv]
    exact (isAlgebraic_natCast (R := ℚ) (A := ℝ) 23).mul
      (isAlgebraic_natCast (R := ℚ) (A := ℝ) 8).inv
  convert tan_sq_half_transcendental (η := (23 / 8 : ℝ)) (by norm_num) ha hc using 1 <;> norm_num

theorem angle_schedule_bounds : 0 < (23 / 8 : ℝ) ∧ (23 / 8 : ℝ) < Real.pi := by
  constructor
  · norm_num
  · linarith [Real.pi_gt_d2]

theorem tan_schedule_gt_one : 1 < Real.tan (23 / 16 : ℝ) := by
  rw [← Real.tan_pi_div_four]
  apply Real.tan_lt_tan_of_nonneg_of_lt_pi_div_two
  · positivity
  · linarith [Real.pi_gt_d2]
  · linarith [Real.pi_lt_d2]

end PhaseEncodedQGE.Schedule



set_option autoImplicit false

namespace PhaseEncodedQGE.Schedule
open Polynomial

@[simp] private theorem qmap (a : ℚ) : algebraMap ℚ ℂ a = (a : ℂ) := by
  simpa only [Rat.cast_id] using map_ratCast (algebraMap ℚ ℂ) a

noncomputable def relationPoly (a b c d : ℚ) : Polynomial ℚ :=
  C (4 * (2 * a + b + 2 * c + d)) * X ^ 55 +
  C (4 * a + 2 * b - 4 * c - 2 * d) * (X ^ 78 + X ^ 32) -
  C (2 * b + 2 * d) * (X ^ 87 + X ^ 23) +
  C (d - b) * (X ^ 110 + 1 + X ^ 64 + X ^ 46)

theorem relationPoly_eq_zero (a b c d : ℚ) (h : relationPoly a b c d = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  have h110 := congrArg (fun p : Polynomial ℚ => p.coeff 110) h
  have h87 := congrArg (fun p : Polynomial ℚ => p.coeff 87) h
  have h55 := congrArg (fun p : Polynomial ℚ => p.coeff 55) h
  have h78 := congrArg (fun p : Polynomial ℚ => p.coeff 78) h
  simp only [relationPoly, mul_add, coeff_add, coeff_sub, coeff_C_mul,
    coeff_X_pow, coeff_one, coeff_zero] at h110 h87 h55 h78
  norm_num at h110 h87 h55 h78
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

noncomputable def spectralS (u : ℂ) : ℂ := (2 - u ^ 32 - (u ^ 32)⁻¹) / 4
noncomputable def spectralT (u : ℂ) : ℂ :=
  (2 - u ^ 23 - (u ^ 23)⁻¹) / (2 + u ^ 23 + (u ^ 23)⁻¹)

theorem relationPoly_eval_zero {u : ℂ} (hu : u ≠ 0)
    (hd : 2 + u ^ 23 + (u ^ 23)⁻¹ ≠ 0)
    (a b c d : ℚ)
    (h : (a : ℂ) + b * spectralS u + c * spectralT u +
      d * spectralT u * spectralS u = 0) :
    Polynomial.aeval u (relationPoly a b c d) = 0 := by
  have h1 : ((a : ℂ) + b * spectralS u) * (2 + u ^ 23 + (u ^ 23)⁻¹) +
      ((c : ℂ) + d * spectralS u) * (2 - u ^ 23 - (u ^ 23)⁻¹) = 0 := by
    have h' : ((a : ℂ) + b * spectralS u) +
        ((c : ℂ) + d * spectralS u) * spectralT u = 0 := by
      linear_combination h
    have hcancel : spectralT u * (2 + u ^ 23 + (u ^ 23)⁻¹) =
        2 - u ^ 23 - (u ^ 23)⁻¹ := div_mul_cancel₀ _ hd
    calc
      _ = (((a : ℂ) + b * spectralS u) +
          ((c : ℂ) + d * spectralS u) * spectralT u) *
          (2 + u ^ 23 + (u ^ 23)⁻¹) := by linear_combination -((c : ℂ) + d * spectralS u) * hcancel
      _ = 0 := by rw [h']; simp
  have h2 := congrArg (fun z : ℂ => (4 * u ^ 55) * z) h1
  simp only [mul_zero] at h2
  convert h2 using 1
  · simp only [relationPoly, map_add, map_sub, map_mul, map_pow, aeval_C, aeval_X,
      map_one, map_ofNat]
    simp only [qmap]
    dsimp [spectralS]
    field_simp [hu]
    <;> ring

theorem spectral_linear_relation {u : ℂ} (hu : u ≠ 0)
    (hd : 2 + u ^ 23 + (u ^ 23)⁻¹ ≠ 0) (ht : Transcendental ℚ u)
    (a b c d : ℚ)
    (h : (a : ℂ) + b * spectralS u + c * spectralT u +
      d * spectralT u * spectralS u = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 :=
  relationPoly_eq_zero a b c d ((transcendental_iff.mp ht) _
    (relationPoly_eval_zero hu hd a b c d h))

end PhaseEncodedQGE.Schedule


set_option autoImplicit false

namespace PhaseEncodedQGE.Schedule

noncomputable def phaseUnit : ℂ := Complex.exp (Complex.I / 8)

theorem phaseUnit_ne_zero : phaseUnit ≠ 0 := Complex.exp_ne_zero _

theorem phaseUnit_transcendental : Transcendental ℚ phaseUnit := by
  apply DiazModulus.hermite_lindemann_holds
  · exact div_ne_zero Complex.I_ne_zero (by norm_num)
  · rw [div_eq_mul_inv]
    exact algebraic_I.mul (isAlgebraic_natCast (R := ℚ) (A := ℂ) 8).inv

theorem phaseUnit_pow (k : ℕ) :
    phaseUnit ^ k = Complex.exp ((((k : ℝ) / 8 : ℝ) : ℂ) * Complex.I) := by
  rw [phaseUnit, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem cos_eighth_multiple (k : ℕ) :
    ((Real.cos ((k : ℝ) / 8) : ℝ) : ℂ) =
      (phaseUnit ^ k + (phaseUnit ^ k)⁻¹) / 2 := by
  rw [Complex.ofReal_cos, Complex.cos, phaseUnit_pow]
  have hn : -(((k : ℝ) / 8 : ℝ) : ℂ) * Complex.I =
      -((((k : ℝ) / 8 : ℝ) : ℂ) * Complex.I) := by ring
  rw [hn, Complex.exp_neg]

theorem spectralS_eq_schedule : spectralS phaseUnit = ((Real.sin 2 ^ 2 : ℝ) : ℂ) := by
  have hc := cos_eighth_multiple 32
  norm_num at hc
  have hs := congrArg Complex.ofReal (Real.sin_sq_eq_half_sub 2)
  push_cast at hs
  norm_num at hs
  rw [hc] at hs
  push_cast
  rw [hs]
  dsimp [spectralS]
  ring

theorem cos_schedule_ne_neg_one : Real.cos (23 / 8 : ℝ) ≠ -1 := by
  intro h
  apply cos_schedule_transcendental
  rw [h]
  exact (isAlgebraic_one (R := ℚ) (A := ℝ)).neg

theorem spectral_denominator_ne_zero : 2 + phaseUnit ^ 23 + (phaseUnit ^ 23)⁻¹ ≠ 0 := by
  intro h
  have hc := cos_eighth_multiple 23
  have hc' : ((Real.cos (23 / 8 : ℝ) : ℝ) : ℂ) = -1 := by
    linear_combination hc + h / 2
  exact cos_schedule_ne_neg_one (by exact_mod_cast hc')

theorem tan_sq_half_formula : Real.tan (23 / 16 : ℝ) ^ 2 =
    (1 - Real.cos (23 / 8 : ℝ)) / (1 + Real.cos (23 / 8 : ℝ)) := by
  have hden : 1 + Real.cos (23 / 8 : ℝ) ≠ 0 := by
    intro h
    apply cos_schedule_ne_neg_one
    linarith
  apply (eq_div_iff hden).mpr
  have hc := Real.cos_eq_two_mul_tan_half_div_one_sub_tan_half_sq
    (23 / 8 : ℝ) cos_schedule_ne_neg_one
  norm_num at hc
  have htden : 1 + Real.tan (23 / 16 : ℝ) ^ 2 ≠ 0 := by positivity
  rw [eq_div_iff htden] at hc
  nlinarith

theorem spectralT_eq_schedule : spectralT phaseUnit = ((Real.tan (23 / 16 : ℝ) ^ 2 : ℝ) : ℂ) := by
  have hc := cos_eighth_multiple 23
  have ht := congrArg Complex.ofReal tan_sq_half_formula
  push_cast at ht
  have hc' : Complex.cos (23 / 8 : ℂ) =
      (phaseUnit ^ 23 + (phaseUnit ^ 23)⁻¹) / 2 := by simpa using hc
  rw [hc'] at ht
  push_cast
  rw [ht]
  dsimp [spectralT]
  field_simp [phaseUnit_ne_zero, spectral_denominator_ne_zero]
  <;> ring

theorem schedule_linearIndependent :
    LinearIndependent ℚ ![(1 : ℝ), Real.sin 2 ^ 2, Real.tan (23 / 16 : ℝ) ^ 2,
      Real.tan (23 / 16 : ℝ) ^ 2 * Real.sin 2 ^ 2] := by
  apply Fintype.linearIndependent_iff.mpr
  intro g hg i
  have hr : (g 0 : ℝ) + (g 1 : ℝ) * Real.sin 2 ^ 2 +
      (g 2 : ℝ) * Real.tan (23 / 16 : ℝ) ^ 2 +
      (g 3 : ℝ) * (Real.tan (23 / 16 : ℝ) ^ 2 * Real.sin 2 ^ 2) = 0 := by
    simpa [Fin.sum_univ_succ, Rat.smul_def, add_assoc] using hg
  have hrC : (g 0 : ℂ) + (g 1 : ℂ) * spectralS phaseUnit +
      (g 2 : ℂ) * spectralT phaseUnit +
      (g 3 : ℂ) * spectralT phaseUnit * spectralS phaseUnit = 0 := by
    rw [spectralS_eq_schedule, spectralT_eq_schedule]
    have hc := congrArg Complex.ofReal hr
    push_cast at hc ⊢
    simpa only [mul_assoc] using hc
  obtain ⟨h0, h1, h2, h3⟩ := spectral_linear_relation phaseUnit_ne_zero
    spectral_denominator_ne_zero phaseUnit_transcendental (g 0) (g 1) (g 2) (g 3) hrC
  fin_cases i <;> assumption

end PhaseEncodedQGE.Schedule

open PhaseEncodedQGE

theorem solution :
    LinearIndependent ℚ ![(1 : ℝ), Real.sin 2 ^ 2, Real.tan ((23 / 8 : ℝ) / 2) ^ 2,
      Real.tan ((23 / 8 : ℝ) / 2) ^ 2 * Real.sin 2 ^ 2] := by
  convert PhaseEncodedQGE.Schedule.schedule_linearIndependent using 1 <;> norm_num
