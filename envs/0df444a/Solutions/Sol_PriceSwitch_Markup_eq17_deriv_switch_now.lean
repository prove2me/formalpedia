-- Prove2me | solution 1 for PriceSwitch.Markup.eq17_deriv_switch_now
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T03:30:28.010059+00:00
-- url     : https://prove2.me/submissions/efde4b5b-d974-451c-a04f-3b68941a2c1a

import Mathlib
import Definitions.Def_PriceSwitch_Markdown_Model

open PriceSwitch.Markdown ProbabilityTheory Finset
open scoped Topology NNReal

private noncomputable def mass (lb : ℝ) (k : ℕ) (t : ℝ) :=
  Real.exp (-(lb * t)) * (lb * t) ^ k / (k.factorial : ℝ)

private lemma mass_deriv_zero (lb t : ℝ) :
    HasDerivAt (mass lb 0) (-lb * mass lb 0 t) t := by
  unfold mass
  simpa [Pi.mul_def, mul_comm] using (((hasDerivAt_id t).const_mul lb).neg.exp)

private lemma mass_deriv_succ (lb t : ℝ) (k : ℕ) :
    HasDerivAt (mass lb (k+1)) (lb * (mass lb k t - mass lb (k+1) t)) t := by
  have h := ((((hasDerivAt_id t).const_mul lb).neg.exp).mul
      (((hasDerivAt_id t).const_mul lb).pow (k+1))).div_const (k+1).factorial
  convert h using 1 <;> try rfl
  simp only [mass, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply, id_eq, mul_one,
    Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, Nat.factorial_succ, Nat.cast_mul]
  have hk : (k.factorial : ℝ) ≠ 0 := by positivity
  have hk1 : (k : ℝ)+1 ≠ 0 := by positivity
  field_simp
  <;> ring

private lemma cdf_deriv (lb t : ℝ) (n : ℕ) :
    HasDerivAt (fun u => ∑ k ∈ range (n+1), mass lb k u) (-lb * mass lb n t) t := by
  induction n with
  | zero => simpa using mass_deriv_zero lb t
  | succ n ih =>
    rw [show (fun u => ∑ k ∈ range (n+1+1), mass lb k u) =
      (fun u => ∑ k ∈ range (n+1), mass lb k u) + mass lb (n+1) by
        ext u; simp only [sum_range_succ, Pi.add_apply]]
    convert ih.add (mass_deriv_succ lb t n) using 1 <;> first | rfl | ring

private lemma tail_deriv (lb t : ℝ) (hlb : 0 ≤ lb) (ht : 0 < t) (n : ℕ) :
    HasDerivAt (fun u => poissonTail (lb*u) (n+1)) (lb * mass lb n t) t := by
  have h := (cdf_deriv lb t n).const_sub 1
  have he : (fun u => poissonTail (lb*u) (n+1)) =ᶠ[𝓝 t]
      (fun u => 1 - ∑ k ∈ range (n+1), mass lb k u) := by
    filter_upwards [eventually_gt_nhds ht] with u hu
    simp [poissonTail, poissonPMFReal, mass, Real.coe_toNNReal _ (mul_nonneg hlb hu.le)]
  convert h.congr_of_eventuallyEq he using 1 <;> first | rfl | ring

private lemma expMin_step (n : ℕ) (m : ℝ) :
    expMinPoisson (n+1) m = expMinPoisson n m + poissonTail m (n+1) := by
  unfold expMinPoisson
  rw [show Icc 1 (n+1) = insert (n+1) (Icc 1 n) by ext j; simp; omega]
  rw [sum_insert (by simp)]
  ring

private lemma expMin_deriv (lb t : ℝ) (hlb : 0 ≤ lb) (ht : 0 < t) (n : ℕ) :
    HasDerivAt (fun u => expMinPoisson n (lb*u)) (lb * (1-poissonTail (lb*t) n)) t := by
  induction n with
  | zero => simpa [expMinPoisson, poissonTail] using hasDerivAt_const t (0 : ℝ)
  | succ n ih =>
    simp_rw [expMin_step]
    convert ih.add (tail_deriv lb t hlb ht n) using 1 <;> try rfl
    simp only [poissonTail, sum_range_succ]
    rw [show poissonPMFReal (lb*t).toNNReal n = mass lb n t by
      simp [poissonPMFReal, mass, Real.coe_toNNReal _ (mul_nonneg hlb ht.le)]]
    ring

private lemma expMin_zero (n : ℕ) : expMinPoisson n 0 = 0 := by
  induction n with
  | zero => simp [expMinPoisson]
  | succ n ih =>
    rw [expMin_step, ih]
    have hs : ∑ k ∈ range (n+1), poissonPMFReal (0 : ℝ≥0) k = 1 := by
      rw [sum_eq_single 0]
      · simp [poissonPMFReal]
      · intro k _ hk; simp [poissonPMFReal, hk]
      · simp
    simp [poissonTail, hs]

theorem solution
    (a la b lb : ℝ) (hlb : 0 ≤ lb) (n : ℕ) (hn : 1 ≤ n) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun u => PriceSwitch.Markdown.switchRevenue a la b lb n u 0)
      (a * la - la * (PriceSwitch.Markdown.switchRevenue a la b lb n t 0 -
        PriceSwitch.Markdown.switchRevenue a la b lb (n - 1) t 0) - PriceSwitch.Markdown.G a la b lb n t) t := by
  have h := (expMin_deriv lb t hlb ht n).const_mul b
  have hstep : expMinPoisson n (lb*t) - expMinPoisson (n-1) (lb*t) = poissonTail (lb*t) n := by
    have hh := expMin_step (n-1) (lb*t)
    rw [show n-1+1=n by omega] at hh
    linarith
  convert h using 1 <;> try rfl
  all_goals simp only [switchRevenue, mul_zero, zero_add, sub_zero, expMin_zero, zero_mul,
    G]
  rw [← mul_sub, hstep]
  ring

#print axioms solution
