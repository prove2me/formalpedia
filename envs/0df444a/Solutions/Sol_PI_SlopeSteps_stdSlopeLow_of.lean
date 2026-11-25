-- Prove2me | solution 1 for PI.SlopeSteps.stdSlopeLow_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:21:34.885174+00:00
-- url     : https://prove2.me/submissions/dfac0ab8-4ced-4767-9e00-e0095a2c11ee

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StandardSlopeBound_NablaBasis
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StandardSlopeBound_StdSlopeLowOf
import Theorems.Thm_PI_SlopeSteps_hwNormPos
import Theorems.Thm_PI_SlopeSteps_natPowPos
import Theorems.Thm_PI_SlopeSteps_sumNuZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.SlopeSteps
open MvPolynomial Formalism.GradedWeylDivisibility
namespace PI.SlopeSteps
theorem _root_.solution (hT2 : NablaGramLow) (hT3 : GramDual) (hT4 : NablaBasis) : PI.StdSlopeLow := by
  intro N ν μ hν ⟨r, e, hr, hμ⟩
  obtain ⟨r', ⟨e'⟩⟩ := hT4 N ν
  obtain ⟨hrr, hdet⟩ := hT3 N ν r r' e e' hν
  subst hrr
  have hlow := hT2 N ν r e' hν
  have hpos := hwNormPos ν
  have hNpow := natPowPos N (∑ s, ν s) (sumNuZero ν)
  have hPpos : (0 : ℚ) < ((∏ s, (ν s).factorial : ℕ) : ℚ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Finset.prod_ne_zero_iff.mpr fun s _ => Nat.factorial_ne_zero _)
  set h := fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν) with hh
  set A : ℚ := ((∏ s, (ν s).factorial : ℕ) : ℚ) / ((N : ℚ) ^ (∑ s, ν s) * h) with hAdef
  have hA : 0 < A := div_pos hPpos (mul_pos hNpow hpos)
  set D := (gramOf ν fun i => (e i : MvPolynomial (Fin N × Fin N) ℤ)).det with hDdef
  set D' := (gramOf ν fun i => (e' i : MvPolynomial (Fin N × Fin N) ℤ)).det with hD'def
  have hD'pos : 0 < D' := lt_of_lt_of_le (pow_pos hA r) hlow
  have hDeq : D = D'⁻¹ := eq_inv_of_mul_eq_one_left hdet
  have hDle : D ≤ (A ^ r)⁻¹ := by rw [hDeq]; exact inv_anti₀ (pow_pos hA r) hlow
  have hDpos : 0 < D := by rw [hDeq]; exact inv_pos.mpr hD'pos
  have hstd : (PI.stdGram ν e).det = D := rfl
  rw [hμ, hstd]
  have hDr : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hDpos
  have hDler : (D : ℝ) ≤ ((A : ℝ) ^ r)⁻¹ := by exact_mod_cast hDle
  have hlog : Real.log (D : ℝ) ≤ -((r : ℝ) * Real.log (A : ℝ)) := by
    calc Real.log (D : ℝ) ≤ Real.log (((A : ℝ) ^ r)⁻¹) := Real.log_le_log hDr hDler
      _ = -((r : ℝ) * Real.log (A : ℝ)) := by rw [Real.log_inv, Real.log_pow]
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  have hlogA : Real.log (A : ℝ) = -((∑ l, (ν l : ℝ)) * Real.log N + Real.log (cNu ν)) := by
    have hP : (0 : ℝ) < ∏ l, ((ν l).factorial : ℝ) :=
      Finset.prod_pos fun l _ => by exact_mod_cast Nat.factorial_pos _
    have hNr : (0 : ℝ) < (N : ℝ) ^ (∑ s, ν s) := by exact_mod_cast hNpow
    have hhr : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hpos
    have hAeq : (A : ℝ) = (∏ l, ((ν l).factorial : ℝ)) / ((N : ℝ) ^ (∑ s, ν s) * (h : ℝ)) := by
      rw [hAdef]; push_cast; ring
    have hc : cNu ν = (h : ℝ) / ∏ l, ((ν l).factorial : ℝ) := rfl
    rw [hAeq, hc, Real.log_div hP.ne' (mul_pos hNr hhr).ne', Real.log_mul hNr.ne' hhr.ne',
      Real.log_div hhr.ne' hP.ne', Real.log_pow]
    push_cast
    ring
  rw [← hlogA, le_div_iff₀ hrpos]
  nlinarith
end PI.SlopeSteps
