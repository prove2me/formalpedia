-- Prove2me | solution 1 for ZetaNine.HarmonicStability.log_den_error_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-02T14:35:57.682288+00:00
-- url     : https://prove2.me/submissions/d2a6b787-fc35-4b24-a05c-3c15d9382fe4

import Definitions.Def_ZetaNine_HarmonicStability
import Mathlib.Data.Rat.Lemmas
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Rational perturbation stability for generalized harmonic denominators

This file formalizes the unconditional denominator inequalities in Lemma 2
of `harmonic-denominator-stability-2026-10-01.md`, their general limit
transfer, and the all-parameter finite lcm clearing bound. It does not assume
or introduce a prime-number-theorem axiom. The harmonic denominator's exact
prime-number-theorem growth rate remains outside this file's current scope.
-/

set_option autoImplicit false

open scoped BigOperators
open Filter

namespace ZetaNine.HarmonicStability



/-- Both divisibilities survive every possible numerator cancellation. -/
theorem denominator_stability (h r : ℚ) :
    (h + r).den ∣ h.den * r.den ∧ h.den ∣ (h + r).den * r.den := by
  constructor
  · exact Rat.add_den_dvd h r
  · simpa only [add_sub_cancel_right] using Rat.sub_den_dvd (h + r) r

theorem logDen_nonneg (q : ℚ) : 0 ≤ logDen q := by
  apply Real.log_nonneg
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Rat.den_nz q)

private theorem logDen_le_logDen_add (h r : ℚ) :
    logDen (h + r) ≤ logDen h + logDen r := by
  have hd := (denominator_stability h r).1
  have hle : (h + r).den ≤ h.den * r.den :=
    Nat.le_of_dvd (Nat.mul_pos (Rat.den_pos h) (Rat.den_pos r)) hd
  have hr : (h + r).den > 0 := Rat.den_pos (h + r)
  have hl := Real.log_le_log (show (0 : ℝ) < ((h + r).den : ℝ) by exact_mod_cast hr)
    (show (((h + r).den : ℕ) : ℝ) ≤ ((h.den * r.den : ℕ) : ℝ) by exact_mod_cast hle)
  simpa only [Nat.cast_mul,
    Real.log_mul (show (h.den : ℝ) ≠ 0 by exact_mod_cast Rat.den_nz h)
      (show (r.den : ℝ) ≠ 0 by exact_mod_cast Rat.den_nz r), logDen] using hl

/-- The exact logarithmic form of the original rational perturbation lemma.
There is no restriction on the size or sign of either numerator. -/
theorem log_denominator_stability (h r : ℚ) :
    |logDen (h + r) - logDen h| ≤ logDen r := by
  have hu := logDen_le_logDen_add h r
  have hl : logDen h ≤ logDen (h + r) + logDen r := by
    have ht := logDen_le_logDen_add (h + r) (-r)
    simpa only [add_neg_cancel_right, logDen, Rat.neg_den] using ht
  exact abs_le.mpr ⟨by linarith, by linarith⟩



private theorem den_sum_dvd {ι : Type*} (S : Finset ι) (f : ι → ℚ) (D : ℕ)
    (h : ∀ i ∈ S, (f i).den ∣ D) : (∑ i ∈ S, f i).den ∣ D := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [Finset.sum_insert hi]
    exact (Rat.add_den_dvd_lcm _ _).trans
      (Nat.lcm_dvd (h i (Finset.mem_insert_self _ _))
        (ih (fun j hj => h j (Finset.mem_insert_of_mem hj))))

/-- The finite upper arithmetic bound in the original harmonic-rate proof,
for the actual reduced denominator and the actual finite lcm. -/
theorem harmonic_den_dvd_lcm_power (s N : ℕ) :
    (harmonicPower s N).den ∣ Nat.lcmUpto N ^ s := by
  apply den_sum_dvd
  intro j hj
  have hjpos : 0 < j := (Finset.mem_Icc.mp hj).1
  have hjdvd : j ∣ Nat.lcmUpto N := Finset.dvd_lcm hj
  rw [one_div, ← inv_pow, Rat.den_pow, Rat.inv_natCast_den_of_pos hjpos]
  exact pow_dvd_pow_of_dvd hjdvd s

/-- The finite logarithmic upper bound for the actual harmonic denominator. -/
theorem harmonic_log_den_le_lcm (s N : ℕ) :
    logDen (harmonicPower s N) ≤ (s : ℝ) * Real.log (Nat.lcmUpto N : ℝ) := by
  have hle : (harmonicPower s N).den ≤ Nat.lcmUpto N ^ s :=
    Nat.le_of_dvd (pow_pos (Nat.lcmUpto_pos N) s) (harmonic_den_dvd_lcm_power s N)
  have ht := Real.log_le_log
    (show (0 : ℝ) < ((harmonicPower s N).den : ℝ) by
      exact_mod_cast Rat.den_pos (harmonicPower s N))
    (show (((harmonicPower s N).den : ℕ) : ℝ) ≤ ((Nat.lcmUpto N ^ s : ℕ) : ℝ) by
      exact_mod_cast hle)
  simpa only [Nat.cast_pow, Real.log_pow, logDen] using ht

/-- A sublinear log-denominator perturbation changes the normalized actual
log-denominator by a quantity tending to zero. This theorem does not assume
that the unperturbed sequence has any limiting rate. -/
theorem checked_log_den_error_tendsto_zero {ι : Type*} (l : Filter ι)
    (h r : ι → ℚ) (scale : ι → ℝ) (hscale : ∀ i, 0 ≤ scale i)
    (hr : Tendsto (fun i => logDen (r i) / scale i) l (nhds 0)) :
    Tendsto (fun i => (logDen (h i + r i) - logDen (h i)) / scale i)
      l (nhds 0) := by
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  refine squeeze_zero (g := fun i => logDen (r i) / scale i) (fun i => abs_nonneg _) ?_ hr
  intro i
  change |(logDen (h i + r i) - logDen (h i)) / scale i| ≤ logDen (r i) / scale i
  rw [abs_div, abs_of_nonneg (hscale i)]
  exact div_le_div_of_nonneg_right (log_denominator_stability (h i) (r i)) (hscale i)

/-- General denominator-rate stability, deduced from the actual arithmetic
denominator inequality rather than assumed for the perturbed sequence. -/
theorem log_den_rate_stability {ι : Type*} (l : Filter ι)
    (h r : ι → ℚ) (scale : ι → ℝ) (hscale : ∀ i, 0 ≤ scale i) (a : ℝ)
    (hh : Tendsto (fun i => logDen (h i) / scale i) l (nhds a))
    (hr : Tendsto (fun i => logDen (r i) / scale i) l (nhds 0)) :
    Tendsto (fun i => logDen (h i + r i) / scale i) l (nhds a) := by
  apply tendsto_of_tendsto_of_dist hh
  refine squeeze_zero (g := fun i => logDen (r i) / scale i) (fun i => dist_nonneg) ?_ hr
  intro i
  rw [Real.dist_eq, ← sub_div, abs_div, abs_of_nonneg (hscale i), abs_sub_comm]
  exact div_le_div_of_nonneg_right (log_denominator_stability (h i) (r i)) (hscale i)

/-- The unconditional analytic stability part of the harmonic perturbation
corollary, for the actual harmonic sum and every natural endpoint. -/
theorem harmonic_log_den_error_tendsto_zero (s : ℕ) (r : ℕ → ℚ)
    (hr : Tendsto (fun N => logDen (r N) / (N : ℝ)) atTop (nhds 0)) :
    Tendsto (fun N => (logDen (harmonicPower s N + r N) - logDen (harmonicPower s N)) /
      (N : ℝ)) atTop (nhds 0) :=
  checked_log_den_error_tendsto_zero atTop (harmonicPower s) r (fun N => (N : ℝ))
    (fun N => Nat.cast_nonneg N) hr

/-- Application of the proved general stability theorem to the original
harmonic corollary. The baseline rate `hh` is the separate PNT-dependent
Theorem 1; it is explicitly a hypothesis here, not an unproved Lean axiom. -/
theorem harmonic_log_den_rate_stability (s : ℕ) (r : ℕ → ℚ)
    (hh : Tendsto (fun N => logDen (harmonicPower s N) / (N : ℝ)) atTop (nhds (s : ℝ)))
    (hr : Tendsto (fun N => logDen (r N) / (N : ℝ)) atTop (nhds 0)) :
    Tendsto (fun N => logDen (harmonicPower s N + r N) / (N : ℝ))
      atTop (nhds (s : ℝ)) :=
  log_den_rate_stability atTop (harmonicPower s) r (fun N => (N : ℝ))
    (fun N => Nat.cast_nonneg N) (s : ℝ) hh hr


end ZetaNine.HarmonicStability

open ZetaNine.HarmonicStability

theorem solution {ι : Type*} (l : Filter ι)
    (h r : ι → ℚ) (scale : ι → ℝ) (hscale : ∀ i, 0 ≤ scale i)
    (hr : Tendsto (fun i => logDen (r i) / scale i) l (nhds 0)) :
    Tendsto (fun i => (logDen (h i + r i) - logDen (h i)) / scale i)
      l (nhds 0) := by
  exact ZetaNine.HarmonicStability.checked_log_den_error_tendsto_zero l h r scale hscale hr

#print axioms solution
