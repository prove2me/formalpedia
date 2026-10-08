-- Prove2me | solution 1 for PriceSwitch.UpOrDown.eq16_deriv_switch_now
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T03:35:12.186701+00:00
-- url     : https://prove2.me/submissions/cb246cd1-9e23-43f5-90b9-64f660490abe

import Mathlib
import Definitions.Def_PriceSwitch_Markdown_Model

open PriceSwitch.Markdown ProbabilityTheory
open scoped BigOperators

private noncomputable def mass (k : ℕ) (m : ℝ) : ℝ :=
  Real.exp (-m) * m ^ k / (k.factorial : ℝ)

private theorem mass_deriv_zero (m : ℝ) : HasDerivAt (mass 0) (-mass 0 m) m := by
  convert! (hasDerivAt_neg m).exp using 1
  · ext u; simp [mass]
  · simp [mass]

private theorem mass_deriv_succ (k : ℕ) (m : ℝ) :
    HasDerivAt (mass (k+1)) (mass k m - mass (k+1) m) m := by
  convert! (((hasDerivAt_neg m).exp).mul ((hasDerivAt_id m).pow (k+1))).div_const ((k+1).factorial : ℝ) using 1
  · simp only [mass, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      Nat.add_sub_cancel, pow_succ, Pi.pow_apply, Pi.mul_apply, id_eq]
    field_simp
    <;> ring

private theorem cdf_deriv (n : ℕ) (m : ℝ) :
    HasDerivAt (fun u => ∑ k ∈ Finset.range (n+1), mass k u) (-mass n m) m := by
  induction n with
  | zero => simpa using mass_deriv_zero m
  | succ n ih =>
    convert! ih.add (mass_deriv_succ n m) using 1
    · ext u; simp [Finset.sum_range_succ]
    · ring

private theorem tail_deriv (n : ℕ) (m : ℝ) (hm : 0 < m) :
    HasDerivAt (fun u => poissonTail u (n+1)) (mass n m) m := by
  have hd := (cdf_deriv n m).const_sub 1
  have heq : (fun u => poissonTail u (n+1)) =ᶠ[nhds m]
      (fun u => 1 - ∑ k ∈ Finset.range (n+1), mass k u) := by
    filter_upwards [eventually_gt_nhds hm] with u hu
    simp [poissonTail, poissonPMFReal, mass, Real.coe_toNNReal _ hu.le]
  convert! hd.congr_of_eventuallyEq heq using 1 <;> ring

private theorem tail_zero (n : ℕ) : poissonTail 0 (n+1) = 0 := by
  induction n with
  | zero => simp [poissonTail, poissonPMFReal]
  | succ n ih =>
    simpa [poissonTail, Finset.sum_range_succ, poissonPMFReal] using ih

private theorem expMin_zero (n : ℕ) : expMinPoisson n 0 = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := (Finset.mem_Icc.mp hj).1; omega : j ≠ 0)
  exact tail_zero k

private theorem expMin_step (n : ℕ) (m : ℝ) :
    expMinPoisson (n+1) m = expMinPoisson n m + poissonTail m (n+1) := by
  unfold expMinPoisson
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n+1)]

private theorem expMin_deriv (n : ℕ) (m : ℝ) (hm : 0 < m) :
    HasDerivAt (expMinPoisson n) (1 - poissonTail m n) m := by
  induction n with
  | zero => convert! hasDerivAt_const m (0 : ℝ) using 1 <;> simp [expMinPoisson, poissonTail]
  | succ n ih =>
    have hh := ih.add (tail_deriv n m hm)
    convert! hh using 1
    · ext u; exact expMin_step n u
    · simp only [poissonTail, Finset.sum_range_succ, mass, poissonPMFReal,
        Real.coe_toNNReal _ hm.le]
      ring

private theorem switch_zero (a la b lb : ℝ) (n : ℕ) (t : ℝ) :
    switchRevenue a la b lb n t 0 = b * expMinPoisson n (lb*t) := by
  simp [switchRevenue, expMin_zero]

theorem solution
    (a la b lb : ℝ) (hlb : 0 ≤ lb) (n : ℕ) (hn : 1 ≤ n) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun u => PriceSwitch.Markdown.switchRevenue a la b lb n u 0)
      (a * la - la * (PriceSwitch.Markdown.switchRevenue a la b lb n t 0 -
        PriceSwitch.Markdown.switchRevenue a la b lb (n - 1) t 0) - PriceSwitch.Markdown.G a la b lb n t) t := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hdiff : switchRevenue a la b lb (k+1) t 0 - switchRevenue a la b lb k t 0 =
      b * poissonTail (lb*t) (k+1) := by
    rw [switch_zero, switch_zero, expMin_step]
    ring
  by_cases hb : lb = 0
  · subst lb
    simpa [switchRevenue, expMin_zero, G, tail_zero] using hasDerivAt_const t (0 : ℝ)
  · have hd := ((expMin_deriv (k+1) (lb*t) (mul_pos (lt_of_le_of_ne hlb (Ne.symm hb)) ht)).comp t
      ((hasDerivAt_id t).const_mul lb)).const_mul b
    convert! hd using 1
    · ext u; exact switch_zero a la b lb (k+1) u
    · simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel, hdiff, G]
      ring

#print axioms solution
