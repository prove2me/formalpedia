-- Prove2me | solution 1 for PrimePairSieve.reciprocal_log_square_kernel_integral
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T11:45:12.232975+00:00
-- url     : https://prove2.me/submissions/013540ae-83fd-47ef-a549-cd72cff0d290

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic

open Real MeasureTheory Set Filter
open scoped BigOperators Topology

noncomputable section
set_option autoImplicit false

private lemma continuousOn_mul_log_sq :
    ContinuousOn (fun x : ℝ => x * Real.log x ^ 2) (Ici 0) := by
  have h := ((Real.continuous_mul_log.comp Real.continuous_sqrt).pow 2).const_mul 4
  refine h.continuousOn.congr ?_
  intro x hx
  dsimp
  rw [Real.log_sqrt hx]
  nlinarith [Real.sq_sqrt hx]

private def momentPrimitive (n : ℕ) (x : ℝ) : ℝ :=
  x ^ (n + 1) * (Real.log x ^ 2 / ((n : ℝ) + 1) -
    2 * Real.log x / ((n : ℝ) + 1) ^ 2 + 2 / ((n : ℝ) + 1) ^ 3)

private lemma momentPrimitive_continuous (n : ℕ) :
    ContinuousOn (momentPrimitive n) (Ici 0) := by
  have h := ((continuousOn_mul_log_sq.div_const ((n : ℝ) + 1)).sub
    (Real.continuous_mul_log.continuousOn.const_mul 2 |>.div_const (((n : ℝ) + 1) ^ 2))).add
    (continuous_id.continuousOn.const_mul 2 |>.div_const (((n : ℝ) + 1) ^ 3))
  have hp := (continuous_id.pow n).continuousOn.mul h
  refine hp.congr ?_
  intro x _
  dsimp [momentPrimitive]
  rw [pow_succ]
  ring

private lemma momentPrimitive_deriv (n : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (momentPrimitive n) (x ^ n * Real.log x ^ 2) x := by
  have hl := Real.hasDerivAt_log hx.ne'
  have h := ((hasDerivAt_id x).pow (n + 1)).mul
    (((hl.pow 2).div_const ((n : ℝ) + 1)).sub
      ((hl.const_mul 2).div_const (((n : ℝ) + 1) ^ 2)) |>.add
      (hasDerivAt_const x (2 / ((n : ℝ) + 1) ^ 3)))
  convert h using 1 <;> try rfl
  dsimp only [id, Pi.mul_apply, Pi.pow_apply, Pi.sub_apply, Pi.add_apply]
  simp only [Nat.cast_add, Nat.cast_one, Nat.add_one_sub_one, mul_one,
    pow_one, add_zero]
  rw [pow_succ]
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hn, hx.ne']
  ring

private lemma moment_integrable (n : ℕ) :
    IntegrableOn (fun x : ℝ => x ^ n * Real.log x ^ 2) (Ioc 0 1) := by
  apply intervalIntegral.integrableOn_deriv_of_nonneg
    ((momentPrimitive_continuous n).mono (fun _ h => h.1))
  · intro x hx
    exact momentPrimitive_deriv n hx.1
  · intro x hx
    exact mul_nonneg (pow_nonneg hx.1.le _) (sq_nonneg _)

private lemma moment_integral (n : ℕ) :
    (∫ x in Ioc (0 : ℝ) 1, x ^ n * Real.log x ^ 2) =
      2 / ((n : ℝ) + 1) ^ 3 := by
  rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have hint : IntervalIntegrable (fun x : ℝ => x ^ n * Real.log x ^ 2) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr (moment_integrable n)
  have hz : Tendsto (momentPrimitive n) (𝓝[>] 0) (𝓝 0) := by
    simpa [momentPrimitive] using
      ((momentPrimitive_continuous n).continuousWithinAt (by simp)).tendsto.mono_left
        (nhdsWithin_mono 0 Ioi_subset_Ici_self)
  have ho : Tendsto (momentPrimitive n) (𝓝[<] 1)
      (𝓝 (2 / ((n : ℝ) + 1) ^ 3)) := by
    simpa [momentPrimitive] using
      (momentPrimitive_deriv n (by norm_num : (0 : ℝ) < 1)).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto (by norm_num)
    (fun x hx => momentPrimitive_deriv n hx.1) hint hz ho]
  ring

private lemma basel_shift :
    HasSum (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ 2) (Real.pi ^ 2 / 6) := by
  have h := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
  simpa using h

set_option maxHeartbeats 600000 in
private lemma alternating_basel :
    HasSum (fun n : ℕ => (-1 : ℝ) ^ n / ((n : ℝ) + 1) ^ 2) (Real.pi ^ 2 / 12) := by
  let f : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) ^ 2
  have hf : HasSum f (Real.pi ^ 2 / 6) := basel_shift
  have he : Summable (fun k : ℕ => f (2 * k)) :=
    hf.summable.comp_injective (fun _ _ h => by omega)
  have ho : HasSum (fun k : ℕ => f (2 * k + 1)) ((Real.pi ^ 2 / 6) / 4) := by
    convert hf.mul_left (1 / 4 : ℝ) using 1 <;> try rfl
    · ext k
      dsimp [f]
      push_cast
      field_simp
      ring
    · ring
  have hsplit := tsum_even_add_odd he ho.summable
  rw [hf.tsum_eq, ho.tsum_eq] at hsplit
  have hev : HasSum (fun k : ℕ => f (2 * k)) (3 * (Real.pi ^ 2 / 6) / 4) := by
    convert he.hasSum using 1 <;> try rfl
    linarith
  have hge : HasSum
      (fun k : ℕ => (-1 : ℝ) ^ (2 * k) / (((2 * k : ℕ) : ℝ) + 1) ^ 2)
      (3 * (Real.pi ^ 2 / 6) / 4) := by
    convert hev using 1 <;> try rfl
    ext k
    simp [f, pow_mul]
  have hgo : HasSum
      (fun k : ℕ => (-1 : ℝ) ^ (2 * k + 1) / (((2 * k + 1 : ℕ) : ℝ) + 1) ^ 2)
      (-((Real.pi ^ 2 / 6) / 4)) := by
    convert ho.neg using 1 <;> try rfl
    ext k
    simp [f, pow_add, pow_mul, div_eq_mul_inv]
  convert HasSum.even_add_odd (f := fun n : ℕ => (-1 : ℝ) ^ n / ((n : ℝ) + 1) ^ 2) hge hgo using 1 <;> try rfl
  ring

private def logKernelTerm (n : ℕ) (x : ℝ) : ℝ :=
  ((n : ℝ) + 1) * (-x) ^ n * Real.log x ^ 2

private lemma logKernelTerm_eq (n : ℕ) (x : ℝ) :
    logKernelTerm n x = (((n : ℝ) + 1) * (-1 : ℝ) ^ n) *
      (x ^ n * Real.log x ^ 2) := by
  dsimp [logKernelTerm]
  rw [neg_pow]
  ring

private lemma term_integrable (n : ℕ) :
    IntegrableOn (logKernelTerm n) (Ioc (0 : ℝ) 1) := by
  rw [show logKernelTerm n = fun x => (((n : ℝ) + 1) * (-1 : ℝ) ^ n) *
    (x ^ n * Real.log x ^ 2) from funext (logKernelTerm_eq n)]
  exact (moment_integrable n).const_mul _

private lemma term_integral (n : ℕ) :
    (∫ x in Ioc (0 : ℝ) 1, logKernelTerm n x) =
      2 * (-1 : ℝ) ^ n / ((n : ℝ) + 1) ^ 2 := by
  simp_rw [logKernelTerm_eq]
  rw [integral_const_mul, moment_integral]
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hn]

private lemma term_norm_integral (n : ℕ) :
    (∫ x in Ioc (0 : ℝ) 1, ‖logKernelTerm n x‖) =
      2 / ((n : ℝ) + 1) ^ 2 := by
  have heq : (fun x => ‖logKernelTerm n x‖) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
      (fun x => ((n : ℝ) + 1) * (x ^ n * Real.log x ^ 2)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    simp only [logKernelTerm, norm_mul, norm_pow, norm_neg, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) + 1), abs_of_nonneg hx.1.le, sq_abs]
    ring
  rw [integral_congr_ae heq, integral_const_mul, moment_integral]
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hn]

/-- The logarithmic-square moment in the reciprocal sieve denominator's centre transform. -/
theorem solution :
    (∫ x in Ioc (0 : ℝ) 1, Real.log x ^ 2 / (1 + x) ^ 2) = Real.pi ^ 2 / 6 := by
  have hnorm : Summable (fun n : ℕ => ∫ x in Ioc (0 : ℝ) 1, ‖logKernelTerm n x‖) := by
    simp_rw [term_norm_integral]
    simpa only [mul_one_div] using basel_shift.summable.mul_left (2 : ℝ)
  have hseries := hasSum_integral_of_summable_integral_norm
    (μ := volume.restrict (Ioc (0 : ℝ) 1)) term_integrable hnorm
  have hvalue : HasSum (fun n : ℕ => ∫ x in Ioc (0 : ℝ) 1, logKernelTerm n x)
      (Real.pi ^ 2 / 6) := by
    convert alternating_basel.mul_left (2 : ℝ) using 1 <;> try rfl
    · ext n
      rw [term_integral]
      ring
    · ring
  have heq : (fun x => ∑' n : ℕ, logKernelTerm n x) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
      (fun x => Real.log x ^ 2 / (1 + x) ^ 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    by_cases hx1 : x = 1
    · subst x
      simp [logKernelTerm]
    · have hlt : ‖(-x : ℝ)‖ < 1 := by
        rw [norm_neg, Real.norm_of_nonneg hx.1.le]
        exact lt_of_le_of_ne hx.2 hx1
      have h := (hasSum_choose_mul_geometric_of_norm_lt_one 1 hlt).mul_right
        (Real.log x ^ 2)
      have h' : HasSum (fun n : ℕ => logKernelTerm n x)
          (Real.log x ^ 2 / (1 + x) ^ 2) := by
        convert h using 1 <;> try rfl
        · ext n
          simp only [logKernelTerm, Nat.choose_one_right, Nat.cast_add, Nat.cast_one]
        · simp only [sub_neg_eq_add]
          ring
      exact h'.tsum_eq
  calc
    (∫ x in Ioc (0 : ℝ) 1, Real.log x ^ 2 / (1 + x) ^ 2) =
        ∫ x in Ioc (0 : ℝ) 1, ∑' n : ℕ, logKernelTerm n x := (integral_congr_ae heq).symm
    _ = Real.pi ^ 2 / 6 := hseries.unique hvalue

#print axioms solution
