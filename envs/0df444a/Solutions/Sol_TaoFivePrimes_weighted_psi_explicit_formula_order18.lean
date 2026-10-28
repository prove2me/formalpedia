-- Prove2me | solution 1 for TaoFivePrimes.weighted_psi_explicit_formula_order18
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T19:42:11.627979+00:00
-- url     : https://prove2.me/submissions/9b585000-a6e0-40d3-83de-bb3f3c0cd0d0

import Mathlib
import Definitions.Def_dusart_psi_433_20261014_ExplicitFormula



set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-!
# Exact polynomial integration for the short-interval smoothing weight

The source uses f(t) = (4*t*(1-t))^18 on [0,1]. Rational polynomial arithmetic
can certify its mass and derivative energy without numerical
quadrature. These are ingredients of the analytic proof, not an RH certificate.
-/

open MeasureTheory
open scoped BigOperators

namespace ShortPrimeIntervalWeight18

def qIntegral (N : ℕ) (c : ℕ → ℚ) (e : ℕ → ℕ) (a b : ℚ) : ℚ :=
  ∑ k ∈ Finset.range N,
    c k * ((b^(e k+1) - a^(e k+1)) / (e k+1 : ℚ))

theorem integral_eq_qIntegral (N : ℕ) (c : ℕ → ℚ) (e : ℕ → ℕ) (a b : ℚ) :
    (∫ t in (a : ℝ)..(b : ℝ), ∑ k ∈ Finset.range N, (c k : ℝ) * t^(e k)) =
      (qIntegral N c e a b : ℝ) := by
  rw [intervalIntegral.integral_finsetSum]
  · simp_rw [intervalIntegral.integral_const_mul, integral_pow]
    unfold qIntegral
    push_cast
    rfl
  · intro k _
    exact Continuous.intervalIntegrable (by fun_prop) _ _

/-- Explicit binomial coefficients, so the certificate evaluator is computable. -/
def weightCoeff (j : ℕ) : ℚ := 4^18 * (-1)^(18-j) * (Nat.choose 18 j : ℚ)

def weightExponent (j : ℕ) : ℕ := 18 + (18-j)

def weightIntegral (a b : ℚ) : ℚ := qIntegral 19 weightCoeff weightExponent a b

theorem weight_eq_sum (t : ℝ) :
    (4 * t * (1-t))^18 =
      ∑ j ∈ Finset.range 19, (weightCoeff j : ℝ) * t^(weightExponent j) := by
  rw [mul_pow, mul_pow, sub_eq_add_neg, add_pow]
  simp only [one_pow, one_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  unfold weightCoeff weightExponent
  push_cast
  rw [neg_pow, pow_add]
  ring

theorem integral_weight (a b : ℚ) :
    (∫ t in (a : ℝ)..(b : ℝ), (4*t*(1-t))^18) = (weightIntegral a b : ℝ) := by
  simp_rw [weight_eq_sum]
  exact integral_eq_qIntegral _ _ _ _ _

theorem weight_mass_pos : 0 < weightIntegral 0 1 := by decide +kernel

theorem real_weight_mass_pos :
    0 < ∫ t in (0 : ℝ)..1, (4*t*(1-t))^18 := by
  have h := integral_weight 0 1
  norm_num only [Rat.cast_zero, Rat.cast_one] at h
  rw [h]
  exact_mod_cast weight_mass_pos

def derivativeCoeff (n j : ℕ) : ℚ :=
  weightCoeff j * (Nat.descFactorial (weightExponent j) n : ℚ)

def derivativeExponent (n j : ℕ) : ℕ := weightExponent j - n

theorem iteratedDeriv_weight (n : ℕ) (t : ℝ) :
    iteratedDeriv n (fun x : ℝ => (4*x*(1-x))^18) t =
      ∑ j ∈ Finset.range 19, (derivativeCoeff n j : ℝ)*t^(derivativeExponent n j) := by
  have heq : (fun x : ℝ => (4*x*(1-x))^18) =
      (fun x : ℝ => ∑ j ∈ Finset.range 19, (weightCoeff j : ℝ)*x^(weightExponent j)) :=
    funext weight_eq_sum
  rw [heq, iteratedDeriv_fun_sum]
  · simp [derivativeCoeff, derivativeExponent, mul_assoc]
  · intro j _
    fun_prop

theorem derivative_at_one_certificate :
    ∀ n ∈ Finset.range 18, (∑ j ∈ Finset.range 19, derivativeCoeff n j) = 0 := by
  decide +kernel

theorem lower_endpoint_vanishing (n : ℕ) (hn : n < 18) :
    iteratedDeriv n (fun x : ℝ => (4*x*(1-x))^18) 0 = 0 := by
  rw [iteratedDeriv_weight]
  apply Finset.sum_eq_zero
  intro j _
  have hpos : 0 < derivativeExponent n j := by
    unfold derivativeExponent weightExponent
    omega
  simp [zero_pow hpos.ne']

theorem upper_endpoint_vanishing (n : ℕ) (hn : n < 18) :
    iteratedDeriv n (fun x : ℝ => (4*x*(1-x))^18) 1 = 0 := by
  rw [iteratedDeriv_weight]
  simp only [one_pow, mul_one]
  exact_mod_cast derivative_at_one_certificate n (Finset.mem_range.mpr hn)

def qEnergy (N : ℕ) (c : ℕ → ℚ) (e : ℕ → ℕ) (a b : ℚ) : ℚ :=
  ∑ i ∈ Finset.range N, qIntegral N (fun j => c i*c j) (fun j => e i+e j) a b

theorem integral_square_eq_qEnergy (N : ℕ) (c : ℕ → ℚ) (e : ℕ → ℕ) (a b : ℚ) :
    (∫ t in (a : ℝ)..(b : ℝ), (∑ j ∈ Finset.range N, (c j : ℝ)*t^(e j))^2) =
      (qEnergy N c e a b : ℝ) := by
  have heq (t : ℝ) : (∑ j ∈ Finset.range N, (c j : ℝ)*t^(e j))^2 =
      ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
        ((c i*c j : ℚ) : ℝ)*t^(e i+e j) := by
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    push_cast
    rw [pow_add]
    ring
  simp_rw [heq]
  rw [intervalIntegral.integral_finsetSum]
  · simp_rw [integral_eq_qIntegral]
    exact_mod_cast (rfl : (∑ i ∈ Finset.range N,
      qIntegral N (fun j => c i*c j) (fun j => e i+e j) a b) = qEnergy N c e a b)
  · intro i _
    exact Continuous.intervalIntegrable (by fun_prop) _ _

theorem weight_mass_exact :
    weightIntegral 0 1 = (4 : ℚ)^18 * (Nat.factorial 18 : ℚ)^2 / Nat.factorial 37 := by
  decide +kernel

theorem derivative_energy_exact :
    qEnergy 19 (derivativeCoeff 18) (derivativeExponent 18) 0 1 =
      (4 : ℚ)^36 * (Nat.factorial 18 : ℚ)^2 / 37 := by
  decide +kernel

theorem real_derivative_energy :
    (∫ t in (0 : ℝ)..1, (iteratedDeriv 18 (fun x : ℝ => (4*x*(1-x))^18) t)^2) =
      (((4 : ℚ)^36 * (Nat.factorial 18 : ℚ)^2 / 37 : ℚ) : ℝ) := by
  simp_rw [iteratedDeriv_weight]
  have h := integral_square_eq_qEnergy 19 (derivativeCoeff 18) (derivativeExponent 18) 0 1
  simp only [Rat.cast_zero, Rat.cast_one] at h
  rw [h, derivative_energy_exact]

theorem integral_abs_sq_le (g : ℝ → ℝ) (hg : Continuous g) :
    (∫ t in (0 : ℝ)..1, |g t|)^2 ≤ ∫ t in (0 : ℝ)..1, (g t)^2 := by
  let I : ℝ := ∫ t in (0 : ℝ)..1, |g t|
  have hnon : 0 ≤ ∫ t in (0 : ℝ)..1, (|g t|-I)^2 :=
    intervalIntegral.integral_nonneg (by norm_num) (fun _ _ => sq_nonneg _)
  have heq : (fun t : ℝ => (|g t|-I)^2) =
      (fun t : ℝ => (g t)^2 - (2*I)*|g t| + I^2) := by
    funext t
    nlinarith [sq_abs (g t)]
  rw [heq, intervalIntegral.integral_add, intervalIntegral.integral_sub,
    intervalIntegral.integral_const_mul] at hnon
  · simp only [intervalIntegral.integral_const, sub_zero, one_smul] at hnon
    dsimp [I] at hnon
    nlinarith
  all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _

def derivativeRatio : ℚ := (Nat.factorial 37 : ℚ) / (Nat.factorial 18 * 6)

theorem derivativeRatio_pos : 0 < derivativeRatio := by decide +kernel

theorem derivative_energy_bound :
    (4 : ℚ)^36 * (Nat.factorial 18 : ℚ)^2 / 37 ≤
      (weightIntegral 0 1)^2 * derivativeRatio^2 := by
  rw [weight_mass_exact]
  decide +kernel

theorem weight_contDiff : ContDiff ℝ ⊤ (fun t : ℝ => (4*t*(1-t))^18) := by
  fun_prop

theorem derivative_l1_of_energy (n : ℕ) (cap : ℚ) (hcap : 0 ≤ cap)
    (he : qEnergy 19 (derivativeCoeff n) (derivativeExponent n) 0 1 ≤
      (weightIntegral 0 1)^2 * cap^2) :
    (∫ t in (0 : ℝ)..1, |iteratedDeriv n (fun x : ℝ => (4*x*(1-x))^18) t|) ≤
      (∫ t in (0 : ℝ)..1, (4*t*(1-t))^18) * (cap : ℝ) := by
  have hd : Continuous (iteratedDeriv n (fun x : ℝ => (4*x*(1-x))^18)) := by
    rw [show iteratedDeriv n (fun x : ℝ => (4*x*(1-x))^18) =
      (fun t : ℝ => ∑ j ∈ Finset.range 19,
        (derivativeCoeff n j : ℝ)*t^(derivativeExponent n j)) from funext (iteratedDeriv_weight n)]
    fun_prop
  have hsq := integral_abs_sq_le _ hd
  have henergy : (∫ t in (0 : ℝ)..1,
      (iteratedDeriv n (fun x : ℝ => (4*x*(1-x))^18) t)^2) =
      (qEnergy 19 (derivativeCoeff n) (derivativeExponent n) 0 1 : ℝ) := by
    simp_rw [iteratedDeriv_weight]
    have h := integral_square_eq_qEnergy 19 (derivativeCoeff n) (derivativeExponent n) 0 1
    simpa only [Rat.cast_zero, Rat.cast_one] using h
  rw [henergy] at hsq
  have he' : (qEnergy 19 (derivativeCoeff n) (derivativeExponent n) 0 1 : ℝ) ≤
      (weightIntegral 0 1 : ℝ)^2 * (cap : ℝ)^2 := by exact_mod_cast he
  have hm := real_weight_mass_pos
  have hk : 0 ≤ (cap : ℝ) := by exact_mod_cast hcap
  have hw := integral_weight 0 1
  simp only [Rat.cast_zero, Rat.cast_one] at hw
  rw [hw] at hm ⊢
  nlinarith [mul_nonneg hm.le hk]

theorem derivative_l1_bound :
    (∫ t in (0 : ℝ)..1, |iteratedDeriv 18 (fun x : ℝ => (4*x*(1-x))^18) t|) ≤
      (∫ t in (0 : ℝ)..1, (4*t*(1-t))^18) * (derivativeRatio : ℝ) := by
  apply derivative_l1_of_energy 18 derivativeRatio derivativeRatio_pos.le
  rw [derivative_energy_exact]
  exact derivative_energy_bound

theorem second_derivative_energy_bound :
    qEnergy 19 (derivativeCoeff 2) (derivativeExponent 2) 0 1 ≤
      (weightIntegral 0 1)^2 * 256^2 := by decide +kernel

theorem second_derivative_l1_bound :
    (∫ t in (0 : ℝ)..1, |iteratedDeriv 2 (fun x : ℝ => (4*x*(1-x))^18) t|) ≤
      (∫ t in (0 : ℝ)..1, (4*t*(1-t))^18) * 256 := by
  exact_mod_cast derivative_l1_of_energy 2 256 (by norm_num) second_derivative_energy_bound

end ShortPrimeIntervalWeight18


set_option maxHeartbeats 1000000

/-!
# The weighted second-primitive identity

This connects a smooth weighted Chebyshev count to the second primitive used
by the existing Perron explicit formula. The right derivative convention
preserves the closed upper endpoint of the prime-counting function.
-/

open MeasureTheory Set Filter
open scoped Topology BigOperators

namespace ShortPrimeIntervalWeightedPrimitive

noncomputable def step (c x : ℝ) : ℝ := if c ≤ x then 1 else 0

noncomputable def first (S : Finset ℕ) (a : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ n ∈ S, a n * max (x-n) 0

noncomputable def second (S : Finset ℕ) (a : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ n ∈ S, a n * (max (x-n) 0)^2 / 2

noncomputable def count (S : Finset ℕ) (a : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ n ∈ S, a n * step n x

theorem step_mono (c : ℝ) : Monotone (step c) := by
  intro x y hxy
  unfold step
  split_ifs <;> linarith

theorem max_hasDerivWithinAt_right (c x : ℝ) :
    HasDerivWithinAt (fun y : ℝ => max (y-c) 0) (step c x) (Ioi x) x := by
  by_cases hcx : c ≤ x
  · rw [step, if_pos hcx]
    apply ((hasDerivAt_id x).sub_const c).hasDerivWithinAt.congr
    · intro y hy
      exact max_eq_left (by change x < y at hy; linarith)
    · exact max_eq_left (sub_nonneg.mpr hcx)
  · have hxc : x < c := lt_of_not_ge hcx
    have heq : (fun y : ℝ => max (y-c) 0) =ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [gt_mem_nhds hxc] with y hy
      exact max_eq_right (by linarith)
    have h := (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq heq
    simpa only [step, if_neg hcx] using h.hasDerivWithinAt

theorem second_kernel_hasDerivWithinAt_right (c x : ℝ) :
    HasDerivWithinAt (fun y : ℝ => (max (y-c) 0)^2 / 2)
      (max (x-c) 0) (Ioi x) x := by
  have h := ((max_hasDerivWithinAt_right c x).pow 2).div_const 2
  convert h using 1 <;> try rfl
  by_cases hcx : c ≤ x
  · simp [step, hcx]
  · simp [step, hcx, max_eq_right (by linarith : x-c ≤ 0)]

theorem first_continuous (S : Finset ℕ) (a : ℕ → ℝ) : Continuous (first S a) := by
  unfold first
  fun_prop

theorem second_continuous (S : Finset ℕ) (a : ℕ → ℝ) : Continuous (second S a) := by
  unfold second
  fun_prop

theorem first_hasDerivWithinAt_right (S : Finset ℕ) (a : ℕ → ℝ) (x : ℝ) :
    HasDerivWithinAt (first S a) (count S a x) (Ioi x) x := by
  have h := HasDerivWithinAt.sum (fun n (_ : n ∈ S) =>
    (max_hasDerivWithinAt_right (n : ℝ) x).const_mul (a n))
  convert h using 1 <;> try rfl
  funext t
  simp only [first, Finset.sum_apply]

theorem second_hasDerivWithinAt_right (S : Finset ℕ) (a : ℕ → ℝ) (x : ℝ) :
    HasDerivWithinAt (second S a) (first S a x) (Ioi x) x := by
  have h := HasDerivWithinAt.sum (fun n (_ : n ∈ S) =>
    (second_kernel_hasDerivWithinAt_right n x).const_mul (a n))
  convert h using 1 <;> try rfl
  funext t
  simp only [second, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro n _
  ring

theorem weighted_second_identity (P P' P'' f f' f'' : ℝ → ℝ)
    (hP : Continuous P) (hP' : Continuous P')
    (hPderiv : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivWithinAt P (P' t) (Ioi t) t)
    (hP'deriv : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivWithinAt P' (P'' t) (Ioi t) t)
    (hP'' : IntervalIntegrable P'' volume 0 1)
    (hf : Continuous f) (hf' : Continuous f') (hf'' : Continuous f'')
    (hfderiv : ∀ t, HasDerivAt f (f' t) t)
    (hf'deriv : ∀ t, HasDerivAt f' (f'' t) t)
    (hz : f 0 = 0) (ho : f 1 = 0) (hz' : f' 0 = 0) (ho' : f' 1 = 0) :
    (∫ t in (0 : ℝ)..1, f t * P'' t) = ∫ t in (0 : ℝ)..1, f'' t * P t := by
  have h1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right
    hf.continuousOn hP'.continuousOn
    (fun t _ => (hfderiv t).hasDerivWithinAt)
    (fun t ht => hP'deriv t (by simpa using ht))
    (hf'.intervalIntegrable 0 1) hP''
  have h2 := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right
    hf'.continuousOn hP.continuousOn
    (fun t _ => (hf'deriv t).hasDerivWithinAt)
    (fun t ht => hPderiv t (by simpa using ht))
    (hf''.intervalIntegrable 0 1) (hP'.intervalIntegrable 0 1)
  simp only [hz, ho, hz', ho', zero_mul, sub_self, zero_sub] at h1 h2
  linarith

theorem right_deriv_comp_affine (g g' : ℝ → ℝ)
    (hg : ∀ x, HasDerivWithinAt g (g' x) (Ioi x) x)
    (A B : ℝ) (hB : 0 < B) (t : ℝ) :
    HasDerivWithinAt (fun v => g (A+B*v)) (B*g' (A+B*t)) (Ioi t) t := by
  have ha : HasDerivAt (fun v : ℝ => A+B*v) B t := by
    convert (hasDerivAt_const t A).add ((hasDerivAt_id t).const_mul B) using 1 <;>
      first | rfl | simp only [zero_add, mul_one]
  have hm : MapsTo (fun v : ℝ => A+B*v) (Ioi t) (Ioi (A+B*t)) := by
    intro v hv
    change t < v at hv
    change A+B*t < A+B*v
    simpa only [add_comm] using add_lt_add_left (mul_lt_mul_of_pos_left hv hB) A
  have h := (hg (A+B*t)).comp t ha.hasDerivWithinAt hm
  convert h using 1 <;> first | rfl | ring

theorem count_affine_intervalIntegrable (S : Finset ℕ) (a : ℕ → ℝ)
    (A B : ℝ) (hB : 0 ≤ B) :
    IntervalIntegrable (fun t => count S a (A+B*t)) volume 0 1 := by
  have hm : Monotone (fun t : ℝ => A+B*t) := by
    intro u v huv
    dsimp
    nlinarith
  have h := IntervalIntegrable.sum (μ := volume) S (fun n (_ : n ∈ S) =>
    (((step_mono n).comp hm).intervalIntegrable (a := (0 : ℝ)) (b := 1)).const_mul (a n))
  convert h using 1 <;> try rfl
  funext t
  simp only [count, Finset.sum_apply, Function.comp_apply]

/-- The actual finite counting sum and its second primitive, after an affine
change of variables. The finite sum includes the endpoint n=A+B*t. -/
theorem weighted_finite_count (S : Finset ℕ) (a : ℕ → ℝ) (A B : ℝ) (hB : 0 < B)
    (f f' f'' : ℝ → ℝ) (hf : Continuous f) (hf' : Continuous f') (hf'' : Continuous f'')
    (hfderiv : ∀ t, HasDerivAt f (f' t) t)
    (hf'deriv : ∀ t, HasDerivAt f' (f'' t) t)
    (hz : f 0 = 0) (ho : f 1 = 0) (hz' : f' 0 = 0) (ho' : f' 1 = 0) :
    (∫ t in (0 : ℝ)..1, f'' t * second S a (A+B*t)) =
      B^2 * (∫ t in (0 : ℝ)..1, f t * count S a (A+B*t)) := by
  have hd2 (t : ℝ) : HasDerivWithinAt (fun v => second S a (A+B*v))
      (B*first S a (A+B*t)) (Ioi t) t :=
    right_deriv_comp_affine _ _ (second_hasDerivWithinAt_right S a) A B hB t
  have hd1 (t : ℝ) : HasDerivWithinAt (fun v => B*first S a (A+B*v))
      (B^2*count S a (A+B*t)) (Ioi t) t := by
    have h := (right_deriv_comp_affine _ _ (first_hasDerivWithinAt_right S a) A B hB t).const_mul B
    convert h using 1 <;> first | rfl | ring
  have h := weighted_second_identity (fun t => second S a (A+B*t))
    (fun t => B*first S a (A+B*t)) (fun t => B^2*count S a (A+B*t))
    f f' f''
    ((second_continuous S a).comp (by fun_prop))
    (((first_continuous S a).comp (by fun_prop)).const_mul B)
    (fun t _ => hd2 t) (fun t _ => hd1 t)
    ((count_affine_intervalIntegrable S a A B hB.le).const_mul (B^2))
    hf hf' hf'' hfderiv hf'deriv hz ho hz' ho'
  have heq (t : ℝ) : f t * (B^2*count S a (A+B*t)) =
      B^2*(f t * count S a (A+B*t)) := by ring
  simp_rw [heq] at h
  rw [intervalIntegral.integral_const_mul] at h
  exact h.symm

theorem count_vonMangoldt_eq_psi (N : ℕ) (x : ℝ) (hx : 0 ≤ x) (hN : x ≤ N) :
    count (Finset.Ioc 0 N) ArithmeticFunction.vonMangoldt x = Chebyshev.psi x := by
  classical
  have hfloor : ⌊x⌋₊ ≤ N := Nat.floor_le_of_le hN
  have hsub : Finset.Ioc 0 ⌊x⌋₊ ⊆ Finset.Ioc 0 N := Finset.Ioc_subset_Ioc le_rfl hfloor
  unfold count Chebyshev.psi
  calc
    _ = ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n * step n x := by
      symm
      apply Finset.sum_subset hsub
      intro n hn hn'
      have hnf : ¬n ≤ ⌊x⌋₊ := by
        intro hnf
        exact hn' (Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hn).1, hnf⟩)
      have hnx : ¬(n : ℝ) ≤ x := by
        intro hnx
        exact hnf ((Nat.le_floor_iff hx).mpr hnx)
      simp only [step, if_neg hnx, mul_zero]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      have hnx : (n : ℝ) ≤ x := (Nat.le_floor_iff hx).mp (Finset.mem_Ioc.mp hn).2
      simp only [step, if_pos hnx, mul_one]

/-- Weighted psi is the second primitive paired with the second derivative of
the test function. This is the exact left side of the existing Perron formula. -/
theorem weighted_psi (N : ℕ) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 < B) (hN : A+B ≤ N)
    (f f' f'' : ℝ → ℝ) (hf : Continuous f) (hf' : Continuous f') (hf'' : Continuous f'')
    (hfderiv : ∀ t, HasDerivAt f (f' t) t)
    (hf'deriv : ∀ t, HasDerivAt f' (f'' t) t)
    (hz : f 0 = 0) (ho : f 1 = 0) (hz' : f' 0 = 0) (ho' : f' 1 = 0) :
    (∫ t in (0 : ℝ)..1, f'' t * second (Finset.Ioc 0 N) ArithmeticFunction.vonMangoldt (A+B*t)) =
      B^2 * (∫ t in (0 : ℝ)..1, f t * Chebyshev.psi (A+B*t)) := by
  rw [weighted_finite_count (Finset.Ioc 0 N) ArithmeticFunction.vonMangoldt A B hB
    f f' f'' hf hf' hf'' hfderiv hf'deriv hz ho hz' ho']
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa using ht
  change f t * count (Finset.Ioc 0 N) ArithmeticFunction.vonMangoldt (A+B*t) =
    f t * Chebyshev.psi (A+B*t)
  rw [count_vonMangoldt_eq_psi N (A+B*t) (by nlinarith [ht'.1]) (by nlinarith [ht'.2])]

end ShortPrimeIntervalWeightedPrimitive


noncomputable section
open MeasureTheory Set

namespace ShortPrimeIntervalWeightedSeries

/-- Absolute uniform bounds on a compact interval justify weighting and
integrating the zero series. The index set may be any countable type. -/
theorem weighted_integral_tsum {ι : Type*} [Countable ι]
    (K : ι → ℝ → ℂ) (hK : ∀ i, ContinuousOn (K i) (Icc (0 : ℝ) 1))
    (cap : ι → ℝ) (hc : Summable cap)
    (hbound : ∀ i t, t ∈ Icc (0 : ℝ) 1 → ‖K i t‖ ≤ cap i)
    (g : ℝ → ℂ) (hg : ContinuousOn g (Icc (0 : ℝ) 1)) :
    (∫ t in (0 : ℝ)..1, g t * (∑' i, K i t)) =
      ∑' i, (∫ t in (0 : ℝ)..1, g t * K i t) := by
  let G (i : ι) (t : ℝ) : ℂ := g t * K i t
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have hg' : ContinuousOn g (uIcc (0 : ℝ) 1) := by simpa using hg
  have hGi (i : ι) : IntervalIntegrable (G i) volume 0 1 := by
    have hKi : ContinuousOn (K i) (uIcc (0 : ℝ) 1) := by simpa using hK i
    exact (hg'.mul hKi).intervalIntegrable
  have hnorm (i : ι) : (∫ t in Ioc (0 : ℝ) 1, ‖G i t‖) ≤
      cap i * (∫ t in (0 : ℝ)..1, ‖g t‖) := by
    rw [← intervalIntegral.integral_of_le h01, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on h01 (hGi i).norm
      ((hg'.norm.const_mul (cap i)).intervalIntegrable)
    intro t ht
    dsimp [G]
    rw [norm_mul, mul_comm (cap i)]
    exact mul_le_mul_of_nonneg_left (hbound i t ht) (norm_nonneg _)
  have hsum : Summable (fun i => ∫ t in Ioc (0 : ℝ) 1, ‖G i t‖) :=
    (hc.mul_right (∫ t in (0 : ℝ)..1, ‖g t‖)).of_nonneg_of_le
      (fun _ => integral_nonneg (fun _ => norm_nonneg _)) hnorm
  have h := MeasureTheory.integral_tsum_of_summable_integral_norm
    (fun i => (hGi i).1) hsum
  simp_rw [← tsum_mul_left, intervalIntegral.integral_of_le h01]
  exact h.symm

end ShortPrimeIntervalWeightedSeries


noncomputable section
open MeasureTheory
open scoped BigOperators

namespace ShortPrimeIntervalMainTerm18
open ShortPrimeIntervalWeight18

def f (t : ℝ) : ℝ := (4*t*(1-t))^18

def d2 (t : ℝ) : ℝ := iteratedDeriv 2 f t

def mass : ℝ := ∫ t in (0 : ℝ)..1, f t

def moment (k : ℕ) : ℚ :=
  qIntegral 19 (derivativeCoeff 2) (fun j => derivativeExponent 2 j + k) 0 1

theorem d2_continuous : Continuous d2 :=
  ContDiff.continuous_iteratedDeriv 2 weight_contDiff (by simp)

theorem real_moment (k : ℕ) :
    (∫ t in (0 : ℝ)..1, d2 t * t^k) = (moment k : ℝ) := by
  have heq (t : ℝ) : d2 t * t^k = ∑ j ∈ Finset.range 19,
      (derivativeCoeff 2 j : ℝ) * t^(derivativeExponent 2 j+k) := by
    unfold d2 f
    rw [iteratedDeriv_weight, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [pow_add]
    ring
  simp_rw [heq]
  have h := integral_eq_qIntegral 19 (derivativeCoeff 2)
    (fun j => derivativeExponent 2 j+k) 0 1
  simp only [Rat.cast_zero, Rat.cast_one] at h
  convert h using 1 <;> rfl

theorem moment0 : moment 0 = 0 := by decide +kernel

theorem moment1 : moment 1 = 0 := by decide +kernel

theorem moment2 : moment 2 = 2*weightIntegral 0 1 := by decide +kernel

theorem moment3 : moment 3 = 3*weightIntegral 0 1 := by decide +kernel

theorem real_moment0 : (∫ t in (0 : ℝ)..1, d2 t) = 0 := by
  have h := real_moment 0
  simpa only [pow_zero, mul_one, moment0, Rat.cast_zero] using h

theorem real_moment1 : (∫ t in (0 : ℝ)..1, d2 t*t) = 0 := by
  have h := real_moment 1
  simpa only [pow_one, moment1, Rat.cast_zero] using h

theorem real_moment2 : (∫ t in (0 : ℝ)..1, d2 t*t^2) = 2*mass := by
  rw [real_moment, moment2]
  have h := integral_weight 0 1
  simp only [Rat.cast_zero, Rat.cast_one] at h
  dsimp only [mass, f]
  rw [h]
  push_cast
  rfl

theorem real_moment3 : (∫ t in (0 : ℝ)..1, d2 t*t^3) = 3*mass := by
  rw [real_moment, moment3]
  have h := integral_weight 0 1
  simp only [Rat.cast_zero, Rat.cast_one] at h
  dsimp only [mass, f]
  rw [h]
  push_cast
  rfl

/-- The cubic Perron main term becomes the expected weighted main term. -/
theorem cubic_main (A B : ℝ) :
    (∫ t in (0 : ℝ)..1, d2 t*(A+B*t)^3/6) = B^2*mass*(A+B/2) := by
  have hd := d2_continuous
  have heq : (fun t : ℝ => d2 t*(A+B*t)^3/6) =
      (fun t => (A^3/6)*d2 t + (A^2*B/2)*(d2 t*t) +
        (A*B^2/2)*(d2 t*t^2) + (B^3/6)*(d2 t*t^3)) := by funext t; ring
  rw [heq, intervalIntegral.integral_add, intervalIntegral.integral_add,
    intervalIntegral.integral_add]
  · simp_rw [intervalIntegral.integral_const_mul]
    rw [real_moment0, real_moment1, real_moment2, real_moment3]
    ring
  all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _

/-- The quadratic zeta-at-zero term is independent of the scale after division
by B^2, so it cancels between the two short-interval endpoints. -/
theorem quadratic_main (A B : ℝ) :
    (∫ t in (0 : ℝ)..1, d2 t*(A+B*t)^2/2) = B^2*mass := by
  have hd := d2_continuous
  have heq : (fun t : ℝ => d2 t*(A+B*t)^2/2) =
      (fun t => (A^2/2)*d2 t + (A*B)*(d2 t*t) + (B^2/2)*(d2 t*t^2)) := by funext t; ring
  rw [heq, intervalIntegral.integral_add, intervalIntegral.integral_add]
  · simp_rw [intervalIntegral.integral_const_mul]
    rw [real_moment0, real_moment1, real_moment2]
    ring
  all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _

end ShortPrimeIntervalMainTerm18


noncomputable section
open MeasureTheory Set
namespace ShortPrimeIntervalWeightedFormula18
open ShortPrimeIntervalMainTerm18 (f d2 mass)
open ShortPrimeIntervalWeightedPrimitive (second)

theorem cubic_main_complex (A B : ℝ) :
    (∫ t in (0 : ℝ)..1, (d2 t : ℂ)*(((A+B*t : ℝ) : ℂ)^3/6)) =
      (B : ℂ)^2*(mass : ℂ)*((A+B/2 : ℝ) : ℂ) := by
  calc
    _ = ∫ t in (0 : ℝ)..1, ((d2 t*(A+B*t)^3/6 : ℝ) : ℂ) := by
      apply intervalIntegral.integral_congr
      intro t _
      push_cast
      ring
    _ = ((∫ t in (0 : ℝ)..1, d2 t*(A+B*t)^3/6 : ℝ) : ℂ) := intervalIntegral.integral_ofReal
    _ = _ := by rw [ShortPrimeIntervalMainTerm18.cubic_main]; push_cast; ring

theorem quadratic_main_complex (A B : ℝ) :
    (∫ t in (0 : ℝ)..1, (d2 t : ℂ)*(((A+B*t : ℝ) : ℂ)^2/2)) =
      (B : ℂ)^2*(mass : ℂ) := by
  calc
    _ = ∫ t in (0 : ℝ)..1, ((d2 t*(A+B*t)^2/2 : ℝ) : ℂ) := by
      apply intervalIntegral.integral_congr
      intro t _
      push_cast
      ring
    _ = ((∫ t in (0 : ℝ)..1, d2 t*(A+B*t)^2/2 : ℝ) : ℂ) := intervalIntegral.integral_ofReal
    _ = _ := by rw [ShortPrimeIntervalMainTerm18.quadratic_main]; push_cast; ring

theorem weighted_psi_cast (N : ℕ) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 < B) (hN : A+B ≤ N) :
    (B : ℂ)^2 * ((∫ t in (0 : ℝ)..1, f t*Chebyshev.psi (A+B*t) : ℝ) : ℂ) =
      ∫ t in (0 : ℝ)..1, (d2 t : ℂ)*
        (second (Finset.Ioc 0 N) ArithmeticFunction.vonMangoldt (A+B*t) : ℂ) := by
  have hf : Continuous f := by unfold f; fun_prop
  have hf' : Continuous (iteratedDeriv 1 f) :=
    ContDiff.continuous_iteratedDeriv 1 ShortPrimeIntervalWeight18.weight_contDiff (by simp)
  have hf'' := ShortPrimeIntervalMainTerm18.d2_continuous
  have hd (n : ℕ) (t : ℝ) : HasDerivAt (iteratedDeriv n f) (iteratedDeriv (n+1) f t) t := by
    have h := ContDiff.differentiable_iteratedDeriv n ShortPrimeIntervalWeight18.weight_contDiff (by simp)
    rw [iteratedDeriv_succ]
    convert (h t).hasDerivAt using 1 <;> rfl
  have h := ShortPrimeIntervalWeightedPrimitive.weighted_psi N A B hA hB hN
    f (iteratedDeriv 1 f) d2 hf hf' hf''
    (fun t => by simpa only [iteratedDeriv_zero] using hd 0 t)
    (fun t => hd 1 t)
    (by norm_num [f]) (by norm_num [f])
    (ShortPrimeIntervalWeight18.lower_endpoint_vanishing 1 (by norm_num))
    (ShortPrimeIntervalWeight18.upper_endpoint_vanishing 1 (by norm_num))
  have hc := congrArg Complex.ofReal h
  push_cast at hc
  rw [← intervalIntegral.integral_ofReal] at hc
  calc
    _ = ∫ t in (0 : ℝ)..1, ((d2 t *
      second (Finset.Ioc 0 N) ArithmeticFunction.vonMangoldt (A+B*t) : ℝ) : ℂ) := hc.symm
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro t _
      push_cast
      rfl

/-- Transferring a second-primitive explicit formula to the concrete weighted
psi integral. The kernel continuity/summability and exact primitive formula
are explicit inputs; actual zeta kernels can be substituted directly. -/
theorem weighted_explicit_formula {ι : Type*} [Countable ι]
    (N : ℕ) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 < B) (hN : A+B ≤ N)
    (L : ℂ) (K : ι → ℝ → ℂ)
    (hK : ∀ i, ContinuousOn (K i) (Icc (0 : ℝ) 1))
    (cap : ι → ℝ) (hc : Summable cap)
    (hbound : ∀ i t, t ∈ Icc (0 : ℝ) 1 → ‖K i t‖ ≤ cap i)
    (R : ℝ → ℂ)
    (hformula : ∀ t ∈ Icc (0 : ℝ) 1,
      (second (Finset.Ioc 0 N) ArithmeticFunction.vonMangoldt (A+B*t) : ℂ) =
        ((A+B*t : ℝ) : ℂ)^3/6 - ((A+B*t : ℝ) : ℂ)^2/2*L -
          (∑' i, K i t) + R t) :
    ((∫ t in (0 : ℝ)..1, f t*Chebyshev.psi (A+B*t) : ℝ) : ℂ) =
      (mass : ℂ)*((A+B/2 : ℝ) : ℂ) - (mass : ℂ)*L -
        (∑' i, (∫ t in (0 : ℝ)..1, (d2 t : ℂ)*K i t))/(B : ℂ)^2 +
        (∫ t in (0 : ℝ)..1, (d2 t : ℂ)*R t)/(B : ℂ)^2 := by
  let P : ℝ → ℂ := fun t => second (Finset.Ioc 0 N) ArithmeticFunction.vonMangoldt (A+B*t)
  let Q3 : ℝ → ℂ := fun t => ((A+B*t : ℝ) : ℂ)^3/6
  let Q2 : ℝ → ℂ := fun t => ((A+B*t : ℝ) : ℂ)^2/2*L
  let Z : ℝ → ℂ := fun t => ∑' i, K i t
  let g : ℝ → ℂ := fun t => d2 t
  have hg : Continuous g := Complex.continuous_ofReal.comp ShortPrimeIntervalMainTerm18.d2_continuous
  have hP : Continuous P := Complex.continuous_ofReal.comp
    ((ShortPrimeIntervalWeightedPrimitive.second_continuous _ _).comp (by fun_prop))
  have hQ3 : Continuous Q3 := by dsimp [Q3]; fun_prop
  have hQ2 : Continuous Q2 := by dsimp [Q2]; fun_prop
  have hZ : ContinuousOn Z (Icc (0 : ℝ) 1) := continuousOn_tsum hK hc hbound
  have hR : ContinuousOn R (Icc (0 : ℝ) 1) := by
    apply (((hP.continuousOn.sub hQ3.continuousOn).add hQ2.continuousOn).add hZ).congr
    intro t ht
    have h := hformula t ht
    change P t = Q3 t-Q2 t-Z t+R t at h
    have he : R t = P t-Q3 t+Q2 t+Z t := by linear_combination -h
    simpa only [Pi.sub_apply, Pi.add_apply] using he
  have hZ' : ContinuousOn Z (uIcc (0 : ℝ) 1) := by simpa using hZ
  have hR' : ContinuousOn R (uIcc (0 : ℝ) 1) := by simpa using hR
  have hI3 := (hg.mul hQ3).intervalIntegrable (μ := volume) (0 : ℝ) 1
  have hI2 := (hg.mul hQ2).intervalIntegrable (μ := volume) (0 : ℝ) 1
  have hIZ := (hg.continuousOn.mul hZ').intervalIntegrable (μ := volume)
  have hIR := (hg.continuousOn.mul hR').intervalIntegrable (μ := volume)
  change IntervalIntegrable (fun t => g t*Q3 t) volume 0 1 at hI3
  change IntervalIntegrable (fun t => g t*Q2 t) volume 0 1 at hI2
  change IntervalIntegrable (fun t => g t*Z t) volume 0 1 at hIZ
  change IntervalIntegrable (fun t => g t*R t) volume 0 1 at hIR
  have heq : (∫ t in (0 : ℝ)..1, g t*P t) =
      (∫ t in (0 : ℝ)..1, g t*Q3 t) - (∫ t in (0 : ℝ)..1, g t*Q2 t) -
        (∫ t in (0 : ℝ)..1, g t*Z t) + (∫ t in (0 : ℝ)..1, g t*R t) := by
    calc
      _ = ∫ t in (0 : ℝ)..1, g t*Q3 t-g t*Q2 t-g t*Z t+g t*R t := by
        apply intervalIntegral.integral_congr
        intro t ht
        have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa using ht
        have h := congrArg (fun z => g t*z) (hformula t ht')
        dsimp [P, Q3, Q2, Z] at h ⊢
        linear_combination h
      _ = _ := by
        rw [intervalIntegral.integral_add ((hI3.sub hI2).sub hIZ) hIR,
          intervalIntegral.integral_sub (hI3.sub hI2) hIZ, intervalIntegral.integral_sub hI3 hI2]
  have hq3 : (∫ t in (0 : ℝ)..1, g t*Q3 t) =
      (B : ℂ)^2*(mass : ℂ)*((A+B/2 : ℝ) : ℂ) := cubic_main_complex A B
  have hq2 : (∫ t in (0 : ℝ)..1, g t*Q2 t) = (B : ℂ)^2*(mass : ℂ)*L := by
    have he (t : ℝ) : g t*Q2 t = (g t*(((A+B*t : ℝ) : ℂ)^2/2))*L := by dsimp [Q2]; ring
    simp_rw [he]
    rw [intervalIntegral.integral_mul_const]
    rw [show (∫ t in (0 : ℝ)..1, g t*(((A+B*t : ℝ) : ℂ)^2/2)) =
      (B : ℂ)^2*(mass : ℂ) from quadratic_main_complex A B]
  have hz := ShortPrimeIntervalWeightedSeries.weighted_integral_tsum K hK cap hc hbound g hg.continuousOn
  rw [hq3, hq2, hz] at heq
  have hp := weighted_psi_cast N A B hA hB hN
  change (B : ℂ)^2*((∫ t in (0 : ℝ)..1, f t*Chebyshev.psi (A+B*t) : ℝ) : ℂ) =
    ∫ t in (0 : ℝ)..1, g t*P t at hp
  have hB0 : (B : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hB.ne'
  apply mul_left_cancel₀ (pow_ne_zero 2 hB0)
  calc
    _ = _ := hp.trans heq
    _ = _ := by dsimp [g]; field_simp [hB0]

end ShortPrimeIntervalWeightedFormula18


noncomputable section
open MeasureTheory Set
namespace ShortPrimeIntervalActualFormula18
open DusartSmoothing
open ShortPrimeIntervalMainTerm18 (f d2 mass)

theorem nontrivial_zeros_countable : Countable NontrivialZetaZero := by
  have hs : {ρ : ℂ | RvM.IsNontrivialZero ρ}.Countable := by
    apply (Set.countable_iUnion (fun n : ℕ =>
      (RvM.finite_symmetric_zero_window (n : ℝ)).countable)).mono
    intro ρ hρ
    exact Set.mem_iUnion.mpr ⟨⌈|ρ.im|⌉₊, hρ, Nat.le_ceil _⟩
  exact hs.to_subtype

theorem quadratic_kernel_continuous (rho : ℂ) (hr : 0 < rho.re) (A B : ℝ) :
    Continuous (fun t : ℝ => quadraticKernel (A+B*t) rho) := by
  have hcp := Complex.continuous_ofReal_cpow_const
    (show 0 < (rho+2).re by simp; linarith)
  unfold quadraticKernel
  exact (hcp.comp (by fun_prop)).div_const _

theorem quadratic_kernel_norm_mono (rho : ℂ) (hr : 0 < rho.re)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ‖quadraticKernel a rho‖ ≤ ‖quadraticKernel b rho‖ := by
  have hb : 0 < b := ha.trans_le hab
  unfold quadraticKernel
  rw [norm_div, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos ha,
    Complex.norm_cpow_eq_rpow_re_of_pos hb]
  exact div_le_div_of_nonneg_right
    (Real.rpow_le_rpow ha.le hab (by simp; linarith)) (norm_nonneg _)

/-- The published second-primitive formula with actual zeta kernels, transferred
to the concrete smoothing weight. No RH hypothesis occurs in this formula. -/
theorem weighted_psi_actual (A B : ℝ) (hA : 1 ≤ A) (hB : 0 < B) :
    ((∫ t in (0 : ℝ)..1, f t*Chebyshev.psi (A+B*t) : ℝ) : ℂ) =
      (mass : ℂ)*((A+B/2 : ℝ) : ℂ) - (mass : ℂ)*logDeriv riemannZeta 0 -
        (∑' ρ : NontrivialZetaZero, (∫ t in (0 : ℝ)..1,
          (d2 t : ℂ)*((RvM.zeroMult ρ.val : ℂ)*quadraticKernel (A+B*t) ρ.val)))/(B : ℂ)^2 +
        (∫ t in (0 : ℝ)..1, (d2 t : ℂ)*perronLeftRemainder (A+B*t))/(B : ℂ)^2 := by
  letI : Countable NontrivialZetaZero := nontrivial_zeros_countable
  let K : NontrivialZetaZero → ℝ → ℂ := fun ρ t =>
    (RvM.zeroMult ρ.val : ℂ)*quadraticKernel (A+B*t) ρ.val
  let cap : NontrivialZetaZero → ℝ := fun ρ =>
    ‖(RvM.zeroMult ρ.val : ℂ)*quadraticKernel (A+B) ρ.val‖
  have hK (ρ : NontrivialZetaZero) : ContinuousOn (K ρ) (Icc (0 : ℝ) 1) :=
    ((quadratic_kernel_continuous ρ.val ρ.property.2.1 A B).const_mul _).continuousOn
  have hc : Summable cap :=
    actual_quadratic_zero_series_absolutely_summable (A+B) (by linarith)
  have hb (ρ : NontrivialZetaZero) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖K ρ t‖ ≤ cap ρ := by
    dsimp [K, cap]
    rw [norm_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left
      (quadratic_kernel_norm_mono ρ.val ρ.property.2.1 (A+B*t) (A+B)
        (by nlinarith [ht.1]) (by nlinarith [ht.2])) (norm_nonneg _)
  let N : ℕ := ⌈A+B⌉₊
  have hN : A+B ≤ N := Nat.le_ceil _
  apply ShortPrimeIntervalWeightedFormula18.weighted_explicit_formula N A B
    (by linarith) hB hN (logDeriv riemannZeta 0) K hK cap hc hb
    (fun t => perronLeftRemainder (A+B*t))
  intro t ht
  have htlo : 1 ≤ A+B*t := by nlinarith [ht.1]
  have hthi : A+B*t ≤ N := le_trans (by nlinarith [ht.2]) hN
  have h := secondPsiPrimitive_explicit_formula N (A+B*t) htlo hthi
  convert h using 1 <;> rfl

end ShortPrimeIntervalActualFormula18

theorem solution (A B : ℝ) (hA : 1 ≤ A) (hB : 0 < B) :
  let f : ℝ → ℝ := fun t => (4*t*(1-t))^18
  let d2 : ℝ → ℝ := iteratedDeriv 2 f
  let mass : ℝ := ∫ t in (0 : ℝ)..1, f t
  ((∫ t in (0 : ℝ)..1, f t*Chebyshev.psi (A+B*t) : ℝ) : ℂ) =
    (mass : ℂ)*((A+B/2 : ℝ) : ℂ) - (mass : ℂ)*logDeriv riemannZeta 0 -
      (∑' ρ : DusartSmoothing.NontrivialZetaZero, (∫ t in (0 : ℝ)..1,
        (d2 t : ℂ)*((DusartSmoothing.RvM.zeroMult ρ.val : ℂ)*
          DusartSmoothing.quadraticKernel (A+B*t) ρ.val)))/(B : ℂ)^2 +
      (∫ t in (0 : ℝ)..1, (d2 t : ℂ)*DusartSmoothing.perronLeftRemainder (A+B*t))/(B : ℂ)^2 := by
  exact ShortPrimeIntervalActualFormula18.weighted_psi_actual A B hA hB
