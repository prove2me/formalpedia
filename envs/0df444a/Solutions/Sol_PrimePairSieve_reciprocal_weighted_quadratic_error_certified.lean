-- Prove2me | solution 1 for PrimePairSieve.reciprocal_weighted_quadratic_error_certified
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T13:18:44.390265+00:00
-- url     : https://prove2.me/submissions/93cc9478-4fe6-4ee7-8883-e81219555bf6

-- Partial summation and logarithmic-moment infrastructure adapted from cm_beta,
-- accepted submission 96ce49e2-c728-4c12-8580-1dfcf469c686 (Apache-2.0).
import Theorems.Thm_PrimePairSieve_reciprocal_log_square_kernel_integral
import Theorems.Thm_PrimePairSieve_reciprocal_error_transfer_bound
import Mathlib.NumberTheory.AbelSummation
import Mathlib.Algebra.BigOperators.Module
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic.Convert
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-!
The literal Riesel--Vaughan denominator has reciprocal weight 1/(1+q/z).
See (3.12), printed p.51, and the exact partial-summation identity on p.52
immediately before (3.15). This is not the quadratic taper max(1-q^2/z^2,0).

Its generic transform accepts any real coefficients with zero term zero;
no positivity, asymptotic estimate, or numerical sieve constant is assumed.
-/

open scoped BigOperators
open MeasureTheory

namespace PrimePairConvolution

noncomputable def finiteCumulative (c : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, c n

noncomputable def reciprocalWeightedSum (c : ℕ → ℝ) (z : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊z⌋₊, c n / (1 + (n : ℝ) / z)

private theorem sum_zero_to_eq_positive (c : ℕ → ℝ) (hc0 : c 0 = 0) (N : ℕ) :
    (∑ n ∈ Finset.Icc 0 N, c n) = finiteCumulative c N := by
  rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le N), Finset.sum_cons, hc0, zero_add,
    ← Finset.Icc_add_one_left_eq_Ioc]
  rfl

private theorem reciprocal_weight_eq (z : ℝ) (hz : 0 < z) (n : ℕ) :
    1 / (1 + (n : ℝ) / z) = z / (z + n) := by
  have hn : z + (n : ℝ) ≠ 0 := by positivity
  have hd : 1 + (n : ℝ) / z ≠ 0 := by positivity
  field_simp [hz.ne', hn, hd]

private theorem reciprocal_weight_mul (a z : ℝ) (hz : 0 < z) (n : ℕ) :
    z / (z + n) * a = a / (1 + (n : ℝ) / z) := by
  calc
    _ = a * (z / (z + n)) := by ring
    _ = a * (1 / (1 + (n : ℝ) / z)) := by rw [reciprocal_weight_eq z hz n]
    _ = _ := by ring

/-- Exact real-level partial summation with the original reciprocal weight.
The lower endpoint zero is harmless because c(0)=0; no moment estimate is used. -/
theorem reciprocal_weighted_integral_abel
    (c : ℕ → ℝ) (hc0 : c 0 = 0) (z : ℝ) (hz : 0 < z) :
    reciprocalWeightedSum c z = finiteCumulative c ⌊z⌋₊ / 2 +
      ∫ t in Set.Ioc 0 z, z / (z + t)^2 * finiteCumulative c ⌊t⌋₊ := by
  let f : ℝ → ℝ := fun t => z / (z + t)
  have hden (t : ℝ) (ht : t ∈ Set.Icc 0 z) : z + t ≠ 0 := by
    have := ht.1
    linarith
  have hderiv (t : ℝ) (ht : t ∈ Set.Icc 0 z) :
      HasDerivAt f (-z / (z + t)^2) t := by
    have hd : HasDerivAt (fun y : ℝ => z / (z + y))
        ((0 * (z + t) - z * (0 + 1)) / (z + t)^2) t := by
      convert! (hasDerivAt_const t z).fun_div
        ((hasDerivAt_const t z).fun_add (hasDerivAt_id' t)) (hden t ht) using 1
    simpa only [f, zero_mul, zero_add, mul_one, zero_sub] using hd
  have hcont : ContinuousOn (fun t : ℝ => -z / (z + t)^2) (Set.Icc 0 z) :=
    continuousOn_const.div ((continuousOn_const.add continuousOn_id).pow 2)
      (fun t ht => pow_ne_zero 2 (hden t ht))
  have hint : IntegrableOn (deriv f) (Set.Icc 0 z) :=
    (hcont.congr (fun t ht => (hderiv t ht).deriv)).integrableOn_Icc
  have hs := sum_mul_eq_sub_integral_mul c hz.le
    (fun t ht => (hderiv t ht).differentiableAt) hint
  have hleft : (∑ n ∈ Finset.Icc 0 ⌊z⌋₊, f n * c n) = reciprocalWeightedSum c z := by
    calc
      _ = ∑ n ∈ Finset.Icc 0 ⌊z⌋₊, c n / (1 + (n : ℝ) / z) := by
        apply Finset.sum_congr rfl
        intro n hn
        dsimp [f]
        exact reciprocal_weight_mul (c n) z hz n
      _ = _ := sum_zero_to_eq_positive _ (by simp [hc0]) ⌊z⌋₊
  have hhalf : f z = (1 / 2 : ℝ) := by
    dsimp [f]
    field_simp [hz.ne'] <;> ring
  have hsum (t : ℝ) :
      (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n) = finiteCumulative c ⌊t⌋₊ :=
    sum_zero_to_eq_positive c hc0 ⌊t⌋₊
  have hi : (∫ t in Set.Ioc 0 z,
      deriv f t * ∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n) =
      -(∫ t in Set.Ioc 0 z, z / (z + t)^2 * finiteCumulative c ⌊t⌋₊) := by
    calc
      _ = ∫ t in Set.Ioc 0 z,
          -(z / (z + t)^2 * finiteCumulative c ⌊t⌋₊) := by
        apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
        intro t ht
        change deriv f t * (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n) =
          -(z / (z + t)^2 * finiteCumulative c ⌊t⌋₊)
        rw [(hderiv t ⟨ht.1.le, ht.2⟩).deriv, hsum]
        ring
      _ = _ := integral_neg _
  rw [hleft, hhalf, hsum, hi] at hs
  simpa only [sub_neg_eq_add, one_div, div_eq_mul_inv, one_mul, mul_comm] using hs


end PrimePairConvolution




set_option autoImplicit false

open MeasureTheory Set
open scoped Interval Topology

namespace PrimePairConvolution

/-!
Local analytic infrastructure for the reciprocal weight in Riesel--Vaughan,
On sums of primes (1983), (3.12) and the transform preceding (3.15).
The logarithm-square moment is an actual convergent integral. Its evaluation
is supplied by the previously proved exact kernel theorem.
-/

noncomputable def reciprocalUnitKernel (v : ℝ) : ℝ := 1 / (1 + v)^2

noncomputable def reciprocalLogSquareMoment : ℝ :=
  ∫ v : ℝ in 0..1, Real.log v ^ 2 * reciprocalUnitKernel v

theorem reciprocalUnitKernel_nonneg (v : ℝ) : 0 ≤ reciprocalUnitKernel v :=
  div_nonneg zero_le_one (sq_nonneg _)

theorem reciprocalUnitKernel_le_one (v : ℝ) (hv : 0 ≤ v) :
    reciprocalUnitKernel v ≤ 1 := by
  unfold reciprocalUnitKernel
  apply (div_le_one (by positivity : 0 < (1+v)^2)).mpr
  nlinarith

theorem reciprocalUnitKernel_continuous :
    ContinuousOn reciprocalUnitKernel (Icc 0 1) := by
  apply continuousOn_const.div ((continuousOn_const.add continuousOn_id).pow 2)
  intro v hv
  apply pow_ne_zero 2
  change 1 + v ≠ 0
  linarith [hv.1]

theorem reciprocalUnitKernel_integrable :
    IntervalIntegrable reciprocalUnitKernel volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  simpa only [uIcc_of_le (show (0:ℝ) ≤ 1 by norm_num)] using
    reciprocalUnitKernel_continuous

theorem reciprocalUnitKernel_mass :
    (∫ v : ℝ in 0..1, reciprocalUnitKernel v) = 1/2 := by
  have hc : ContinuousOn (fun v : ℝ => v/(1+v)) (Icc 0 1) :=
    continuousOn_id.div (continuousOn_const.add continuousOn_id)
      (fun v hv => by change 1 + v ≠ 0; linarith [hv.1])
  have hd : ∀ v ∈ Ioo (0:ℝ) 1,
      HasDerivAt (fun v : ℝ => v/(1+v)) (reciprocalUnitKernel v) v := by
    intro v hv
    have h := (hasDerivAt_id' v).fun_div
      ((hasDerivAt_const v (1:ℝ)).fun_add (hasDerivAt_id' v))
      (by change 1 + v ≠ 0; linarith [hv.1])
    convert! h using 1 <;> simp [reciprocalUnitKernel]
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (show (0:ℝ) ≤ 1 by norm_num) hc hd reciprocalUnitKernel_integrable
  norm_num at h ⊢
  exact h

theorem reciprocalUnitKernel_log_integrable :
    IntervalIntegrable (fun v : ℝ => Real.log v * reciprocalUnitKernel v) volume 0 1 := by
  apply intervalIntegral.intervalIntegrable_log'.mul_continuousOn
  simpa only [uIcc_of_le (show (0:ℝ) ≤ 1 by norm_num)] using
    reciprocalUnitKernel_continuous

theorem reciprocalUnitKernel_log_moment :
    (∫ v : ℝ in 0..1, Real.log v * reciprocalUnitKernel v) = -Real.log 2 := by
  let f : ℝ → ℝ := fun v => v * Real.log v / (1+v) - Real.log (1+v)
  have hc : ContinuousOn f (Icc 0 1) := by
    exact (Real.continuous_mul_log.continuousOn.div
      (continuousOn_const.add continuousOn_id)
      (fun v hv => by change 1 + v ≠ 0; linarith [hv.1])).sub
      ((continuousOn_const.add continuousOn_id).log
        (fun v hv => by change 1 + v ≠ 0; linarith [hv.1]))
  have hd : ∀ v ∈ Ioo (0:ℝ) 1,
      HasDerivAt f (Real.log v * reciprocalUnitKernel v) v := by
    intro v hv
    have hv1 : 1+v ≠ 0 := by linarith [hv.1]
    have hd1 := (hasDerivAt_const v (1:ℝ)).fun_add (hasDerivAt_id' v)
    have h := ((Real.hasDerivAt_mul_log hv.1.ne').fun_div hd1 hv1).sub (hd1.log hv1)
    convert! h using 1 <;> simp only [reciprocalUnitKernel]
    <;> field_simp [hv1] <;> ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (show (0:ℝ) ≤ 1 by norm_num) hc hd reciprocalUnitKernel_log_integrable
  simpa only [f, Real.log_one, mul_zero, zero_div, sub_zero, zero_add,
    show (1:ℝ) + 1 = 2 by norm_num,
    zero_mul, add_zero, sub_self, zero_sub] using h

theorem log_sq_le_unit_power (v : ℝ) (hv : 0 < v) (hv1 : v ≤ 1) :
    Real.log v ^ 2 ≤ 36 * v ^ (-(1/3 : ℝ)) := by
  have hp : 0 < v^(1/6 : ℝ) := Real.rpow_pos_of_pos hv _
  have h := (Real.abs_log_mul_self_rpow_lt v (1/6) hv hv1 (by norm_num)).le
  rw [abs_mul, abs_of_pos hp] at h
  norm_num only [one_div_div, div_one] at h
  have hs := pow_le_pow_left₀ (mul_nonneg (abs_nonneg _) hp.le) h 2
  rw [mul_pow, sq_abs, ← Real.rpow_mul_natCast hv.le] at hs
  norm_num at hs
  have hdiv := (le_div_iff₀ (Real.rpow_pos_of_pos hv (1/3 : ℝ))).mpr hs
  simpa only [Real.rpow_neg hv.le, div_eq_mul_inv] using hdiv

/-- The elementary power envelope proves genuine integrability at zero. -/
theorem unit_integrable_of_power_bound (f : ℝ → ℝ) (hf : Measurable f) (A : ℝ)
    (_hA : 0 ≤ A) (hbound : ∀ v, 0 < v → v ≤ 1 → ‖f v‖ ≤ A*v^(-(1/3:ℝ))) :
    IntervalIntegrable f volume 0 1 := by
  have hi : IntervalIntegrable (fun v : ℝ => A*v^(-(1/3:ℝ))) volume 0 1 :=
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1:ℝ) < -(1/3:ℝ))).const_mul A
  apply hi.mono_fun' hf.aestronglyMeasurable
  rw [uIoc_of_le (show (0:ℝ) ≤ 1 by norm_num)]
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
  exact hbound v hv.1 hv.2

theorem reciprocalUnitKernel_log_sq_integrable :
    IntervalIntegrable (fun v : ℝ => Real.log v ^ 2 * reciprocalUnitKernel v) volume 0 1 := by
  have hi : IntervalIntegrable (fun v : ℝ => Real.log v ^ 2) volume 0 1 := by
    apply unit_integrable_of_power_bound _ (Real.measurable_log.pow_const 2) 36 (by norm_num)
    intro v hv hv1
    simpa only [Real.norm_eq_abs, abs_sq] using log_sq_le_unit_power v hv hv1
  apply hi.mul_continuousOn
  simpa only [uIcc_of_le (show (0:ℝ) ≤ 1 by norm_num)] using
    reciprocalUnitKernel_continuous

end PrimePairConvolution



/-!
Append after ReciprocalWeightMoments and ReciprocalWeightedTransform.
Additionally import Mathlib.MeasureTheory.Function.Floor.
All integrals at zero are justified by explicit power domination. The final
finite-sum transfer assumes only an unweighted all-positive error estimate;
it does not assume the weighted conclusion or any numerical coefficient moment.
-/

namespace PrimePairConvolution

noncomputable def reciprocalAverage (F : ℝ → ℝ) (z : ℝ) : ℝ :=
  F z / 2 + ∫ v : ℝ in 0..1, F (z*v) * reciprocalUnitKernel v

noncomputable def logQuadratic (a b d : ℝ) (z : ℝ) : ℝ :=
  a * Real.log z ^ 2 + b * Real.log z + d

theorem finiteCumulative_floor_zero_below_one (c : ℕ → ℝ) (z : ℝ) (hz : z < 1) :
    finiteCumulative c ⌊z⌋₊ = 0 := by
  rw [Nat.floor_eq_zero.mpr hz]
  simp [finiteCumulative]

private theorem reciprocalUnitKernel_measurable : Measurable reciprocalUnitKernel :=
  measurable_const.div ((measurable_const.add measurable_id).pow_const 2)

private theorem logQuadratic_measurable (a b d : ℝ) : Measurable (logQuadratic a b d) :=
  (((Real.measurable_log.pow_const 2).const_mul a).add
    (Real.measurable_log.const_mul b)).add_const d

private theorem logQuadratic_kernel_expand (a b d z v : ℝ) (hz : 0 < z) (hv : 0 < v) :
    logQuadratic a b d (z*v) * reciprocalUnitKernel v =
      a * (Real.log v ^ 2 * reciprocalUnitKernel v) +
      (2*a*Real.log z+b) * (Real.log v * reciprocalUnitKernel v) +
      logQuadratic a b d z * reciprocalUnitKernel v := by
  unfold logQuadratic
  rw [Real.log_mul hz.ne' hv.ne']
  ring

private theorem logQuadratic_kernel_integrable (a b d z : ℝ) (hz : 0 < z) :
    IntervalIntegrable (fun v => logQuadratic a b d (z*v)*reciprocalUnitKernel v)
      volume 0 1 := by
  have h := ((reciprocalUnitKernel_log_sq_integrable.const_mul a).add
    (reciprocalUnitKernel_log_integrable.const_mul (2*a*Real.log z+b))).add
    (reciprocalUnitKernel_integrable.const_mul (logQuadratic a b d z))
  apply h.congr_uIoo
  intro v hv
  rw [uIoo_of_le (show (0:ℝ)≤1 by norm_num)] at hv
  exact (logQuadratic_kernel_expand a b d z v hz hv.1).symm

theorem reciprocalAverage_logQuadratic (a b d z : ℝ) (hz : 0 < z) :
    reciprocalAverage (logQuadratic a b d) z =
      a * Real.log z ^ 2 + (b-2*a*Real.log 2)*Real.log z +
        d-b*Real.log 2+a*reciprocalLogSquareMoment := by
  have hi : (∫ v : ℝ in 0..1, logQuadratic a b d (z*v)*reciprocalUnitKernel v) =
      a*reciprocalLogSquareMoment + (2*a*Real.log z+b)*(-Real.log 2) +
      logQuadratic a b d z*(1/2) := by
    calc
      _ = ∫ v : ℝ in 0..1,
          a*(Real.log v^2*reciprocalUnitKernel v) +
          (2*a*Real.log z+b)*(Real.log v*reciprocalUnitKernel v) +
          logQuadratic a b d z*reciprocalUnitKernel v := by
        apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num : (0:ℝ)≤1)
        intro v hv
        exact logQuadratic_kernel_expand a b d z v hz hv.1
      _ = _ := by
        rw [intervalIntegral.integral_add
          ((reciprocalUnitKernel_log_sq_integrable.const_mul a).add
            (reciprocalUnitKernel_log_integrable.const_mul (2*a*Real.log z+b)))
          (reciprocalUnitKernel_integrable.const_mul (logQuadratic a b d z)),
          intervalIntegral.integral_add (reciprocalUnitKernel_log_sq_integrable.const_mul a)
            (reciprocalUnitKernel_log_integrable.const_mul (2*a*Real.log z+b))]
        simp only [intervalIntegral.integral_const_mul, reciprocalLogSquareMoment,
          reciprocalUnitKernel_log_moment, reciprocalUnitKernel_mass]
  unfold reciprocalAverage
  rw [hi]
  unfold logQuadratic
  ring


end PrimePairConvolution

namespace PrimePairConvolution

private lemma log_square_moment_value : reciprocalLogSquareMoment = Real.pi ^ 2 / 6 := by
  unfold reciprocalLogSquareMoment reciprocalUnitKernel
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  simpa only [mul_one_div] using PrimePairSieve.reciprocal_log_square_kernel_integral

private lemma reciprocalAverage_remainder_certified
    (r : ℝ → ℝ) (hr : Measurable r) (E z : ℝ) (hE : 0 ≤ E) (hz : 0 < z)
    (hbound : ∀ t, 0 < t → |r t| ≤ E * t ^ (-(1 / 3 : ℝ))) :
    |reciprocalAverage r z| ≤ (8479 / 6160 : ℝ) * E * z ^ (-(1 / 3 : ℝ)) := by
  have hscaled (v : ℝ) (hv : 0 < v) :
      |r (z * v)| ≤ (E * z ^ (-(1 / 3 : ℝ))) * v ^ (-(1 / 3 : ℝ)) := by
    simpa only [Real.mul_rpow hz.le hv.le, mul_assoc] using
      hbound (z * v) (mul_pos hz hv)
  have hEm : 0 ≤ E * z ^ (-(1 / 3 : ℝ)) :=
    mul_nonneg hE (Real.rpow_nonneg hz.le _)
  have hi : IntervalIntegrable (fun v => r (z * v)) volume 0 1 := by
    apply unit_integrable_of_power_bound _ (hr.comp (measurable_const.mul measurable_id))
      (E * z ^ (-(1 / 3 : ℝ))) hEm
    intro v hv _
    simpa only [Real.norm_eq_abs, Function.comp_apply, Pi.mul_apply, id_eq] using hscaled v hv
  have h := PrimePairSieve.reciprocal_error_transfer_bound (fun v => r (z * v)) 1
    (E * z ^ (-(1 / 3 : ℝ))) (by norm_num) hEm
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp hi)
    (fun v hv => hscaled v hv.1)
  unfold reciprocalAverage
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  simpa only [mul_one, add_comm (1 : ℝ), reciprocalUnitKernel, mul_one_div,
    mul_comm (r (z * _)), Real.one_rpow, mul_assoc] using h

private lemma reciprocalAverage_quadratic_certified
    (F : ℝ → ℝ) (hF : Measurable F) (a b d E : ℝ) (hE : 0 ≤ E)
    (hbound : ∀ t, 0 < t → |F t - logQuadratic a b d t| ≤ E * t ^ (-(1 / 3 : ℝ)))
    (z : ℝ) (hz : 0 < z) :
    |reciprocalAverage F z -
      (a * Real.log z ^ 2 + (b - 2 * a * Real.log 2) * Real.log z +
        d - b * Real.log 2 + a * Real.pi ^ 2 / 6)| ≤
      (8479 / 6160 : ℝ) * E * z ^ (-(1 / 3 : ℝ)) := by
  let r : ℝ → ℝ := fun t => F t - logQuadratic a b d t
  have hr : Measurable r := hF.sub (logQuadratic_measurable a b d)
  have hiR : IntervalIntegrable (fun v => r (z * v)) volume 0 1 := by
    apply unit_integrable_of_power_bound _ (hr.comp (measurable_const.mul measurable_id))
      (E * z ^ (-(1 / 3 : ℝ))) (mul_nonneg hE (Real.rpow_nonneg hz.le _))
    intro v hv _
    simpa only [Real.norm_eq_abs, Function.comp_apply, Pi.mul_apply, id_eq, r, Real.mul_rpow hz.le hv.le, mul_assoc] using
      hbound (z * v) (mul_pos hz hv)
  have hiRw := hiR.mul_continuousOn (by
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using reciprocalUnitKernel_continuous)
  have hiP := logQuadratic_kernel_integrable a b d z hz
  have hsplit : reciprocalAverage F z =
      reciprocalAverage (logQuadratic a b d) z + reciprocalAverage r z := by
    unfold reciprocalAverage
    have hid : (fun v => F (z * v) * reciprocalUnitKernel v) =
        (fun v => logQuadratic a b d (z * v) * reciprocalUnitKernel v +
          r (z * v) * reciprocalUnitKernel v) := by
      funext v
      dsimp [r]
      ring
    rw [hid, intervalIntegral.integral_add hiP hiRw]
    dsimp [r]
    ring
  rw [hsplit, reciprocalAverage_logQuadratic a b d z hz, log_square_moment_value]
  have hc : a * Real.log z ^ 2 + (b - 2 * a * Real.log 2) * Real.log z +
      d - b * Real.log 2 + a * (Real.pi ^ 2 / 6) =
      a * Real.log z ^ 2 + (b - 2 * a * Real.log 2) * Real.log z +
      d - b * Real.log 2 + a * Real.pi ^ 2 / 6 := by ring
  rw [hc, add_sub_cancel_left]
  exact reciprocalAverage_remainder_certified r hr E z hE hz hbound

private theorem reciprocalWeightedSum_eq_average (c : ℕ → ℝ) (hc0 : c 0 = 0)
    (z : ℝ) (hz : 0 < z) :
    reciprocalWeightedSum c z = reciprocalAverage (fun t => finiteCumulative c ⌊t⌋₊) z := by
  rw [reciprocal_weighted_integral_abel c hc0 z hz]
  unfold reciprocalAverage
  congr 1
  rw [← intervalIntegral.integral_of_le hz.le]
  have hscale := intervalIntegral.mul_integral_comp_mul_left
    (f := fun t : ℝ => z / (z + t) ^ 2 * finiteCumulative c ⌊t⌋₊) (a := 0) (b := 1) z
  simp only [mul_zero, mul_one] at hscale
  rw [← hscale, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro v hv
  rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hv
  have hv1 : 1 + v ≠ 0 := by linarith [hv.1]
  change z * (z / (z + z * v) ^ 2 * finiteCumulative c ⌊z * v⌋₊) =
    finiteCumulative c ⌊z * v⌋₊ * reciprocalUnitKernel v
  unfold reciprocalUnitKernel
  have hden : z + z * v ≠ 0 := by nlinarith [mul_nonneg hz.le hv.1]
  field_simp [hz.ne', hv1, hden]

end PrimePairConvolution

theorem solution (c : ℕ → ℝ) (hc0 : c 0 = 0) (a b d E : ℝ) (hE : 0 ≤ E)
    (hbound : ∀ t : ℝ, 0 < t →
      |(∑ n ∈ Finset.Icc 1 ⌊t⌋₊, c n) -
        (a * Real.log t ^ 2 + b * Real.log t + d)| ≤ E * t ^ (-(1 / 3 : ℝ)))
    (z : ℝ) (hz : 0 < z) :
    |(∑ n ∈ Finset.Icc 1 ⌊z⌋₊, c n / (1 + (n : ℝ) / z)) -
      (a * Real.log z ^ 2 + (b - 2 * a * Real.log 2) * Real.log z +
        d - b * Real.log 2 + a * Real.pi ^ 2 / 6)| ≤
      (8479 / 6160 : ℝ) * E * z ^ (-(1 / 3 : ℝ)) := by
  change |PrimePairConvolution.reciprocalWeightedSum c z - _| ≤ _
  rw [PrimePairConvolution.reciprocalWeightedSum_eq_average c hc0 z hz]
  exact PrimePairConvolution.reciprocalAverage_quadratic_certified _
    ((measurable_of_countable (PrimePairConvolution.finiteCumulative c)).comp Nat.measurable_floor)
    a b d E hE hbound z hz

#print axioms solution
