-- Prove2me | solution 1 for StateIndepNRM.eq_12
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T19:25:42.060695+00:00
-- url     : https://prove2.me/submissions/0d08afe5-9961-4343-8143-f4dc5d1f4714

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Aux_SINeq12

theorem log_bound (u : ℝ) (hu : 0 ≤ u) : 2 * u / (2 + u) ≤ Real.log (1 + u) := by
  let f : ℝ → ℝ := fun v => Real.log (1 + v) - 2 * v / (2 + v)
  have hd : ∀ v, 0 ≤ v → HasDerivAt f (1 / (1 + v) - (2 * (2 + v) - 2 * v * 1) / (2 + v) ^ 2) v := by
    intro v hv
    have h1 : HasDerivAt (fun v : ℝ => 1 + v) 1 v := (hasDerivAt_id v).const_add 1
    have h2 := h1.log (by linarith)
    have h3 : HasDerivAt (fun v : ℝ => 2 * v) 2 v := by
      simpa using (hasDerivAt_id v).const_mul 2
    have h4 : HasDerivAt (fun v : ℝ => 2 + v) 1 v := (hasDerivAt_id v).const_add 2
    have h5 := h3.div h4 (by linarith)
    exact h2.sub h5
  have hmono : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · intro v hv; exact (hd v hv).continuousAt.continuousWithinAt
    · intro v hv
      rw [interior_Ici] at hv
      exact (hd v (le_of_lt hv)).differentiableAt.differentiableWithinAt
    · intro v hv
      rw [interior_Ici] at hv
      have hv' : (0 : ℝ) < v := hv
      rw [(hd v hv'.le).deriv]
      have : 1 / (1 + v) - (2 * (2 + v) - 2 * v * 1) / (2 + v) ^ 2 =
          v ^ 2 / ((1 + v) * (2 + v) ^ 2) := by
        field_simp <;> ring
      rw [this]
      positivity
  have := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hu) hu
  simp only [f, add_zero, Real.log_one, mul_zero, zero_div, sub_zero] at this
  linarith

theorem hexp (y : ℝ) : HasSum (fun n : ℕ => y ^ n / (n.factorial : ℝ)) (Real.exp y) := by
  have := NormedSpace.expSeries_div_hasSum_exp y
  rwa [← Real.exp_eq_exp_ℝ] at this

end Aux_SINeq12

open Aux_SINeq12 in
theorem solution (r : ℝ≥0) (hr : 0 < r) (x : ℝ) (hx : 0 ≤ x) :
    (poissonMeasure r).real {j : ℕ | (r : ℝ) + x ≤ j} ≤
      Real.exp (-(x ^ 2 / (2 * ((r : ℝ) + x)))) := by
  set R : ℝ := (r : ℝ) with hRdef
  have hR : 0 < R := by simpa [hRdef] using hr
  set a : ℝ := R + x with ha
  have ha0 : 0 < a := by linarith
  set S : Set ℕ := {j : ℕ | R + x ≤ j} with hS
  set t : ℝ := Real.log (1 + x / R) with ht
  have h1x : 0 < 1 + x / R := by positivity
  have hxR : 0 ≤ x / R := by positivity
  have ht0 : 0 ≤ t := Real.log_nonneg (by linarith)
  have het : Real.exp t = 1 + x / R := Real.exp_log h1x
  -- probability as a sum
  have hP : (poissonMeasure r).real S =
      ∑' n : ℕ, Real.exp (-R) * R ^ n / (n.factorial : ℝ) * S.indicator 1 n := by
    rw [← integral_indicator_one (MeasurableSet.of_discrete), integral_poissonMeasure]
    simp [smul_eq_mul, hRdef]
  set g : ℕ → ℝ := fun n => Real.exp (-R) * R ^ n / (n.factorial : ℝ) * Real.exp (t * (n - a))
    with hg
  have hgsum : HasSum g (Real.exp (-R) * Real.exp (-(t * a)) * Real.exp (R * Real.exp t)) := by
    have := (hexp (R * Real.exp t)).mul_left (Real.exp (-R) * Real.exp (-(t * a)))
    have hfun : g = fun i : ℕ => Real.exp (-R) * Real.exp (-(t * a)) *
        ((R * Real.exp t) ^ i / (i.factorial : ℝ)) := by
      funext n
      simp only [hg]
      rw [show t * ((n : ℝ) - a) = (n : ℝ) * t + -(t * a) by ring, Real.exp_add,
        Real.exp_nat_mul, mul_pow]
      ring
    rw [hfun]
    exact this
  have hle : ∀ n : ℕ, Real.exp (-R) * R ^ n / (n.factorial : ℝ) * S.indicator 1 n ≤ g n := by
    intro n
    simp only [hg]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    by_cases hn : n ∈ S
    · rw [Set.indicator_of_mem hn]
      simp only [Pi.one_apply]
      apply Real.one_le_exp
      apply mul_nonneg ht0
      simp only [hS, Set.mem_setOf_eq] at hn
      linarith
    · rw [Set.indicator_of_notMem hn]
      exact (Real.exp_pos _).le
  have hnn : ∀ n : ℕ, 0 ≤ Real.exp (-R) * R ^ n / (n.factorial : ℝ) * S.indicator 1 n := by
    intro n
    apply mul_nonneg (by positivity)
    by_cases hn : n ∈ S
    · rw [Set.indicator_of_mem hn]; norm_num
    · rw [Set.indicator_of_notMem hn]
  have hfs : Summable (fun n : ℕ => Real.exp (-R) * R ^ n / (n.factorial : ℝ) * S.indicator 1 n) :=
    Summable.of_nonneg_of_le hnn hle hgsum.summable
  have hbound : (poissonMeasure r).real S ≤
      Real.exp (-R) * Real.exp (-(t * a)) * Real.exp (R * Real.exp t) := by
    rw [hP, ← hgsum.tsum_eq]
    exact hfs.tsum_le_tsum hle hgsum.summable
  refine hbound.trans ?_
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  rw [het]
  have hlb := log_bound (x / R) (by positivity)
  have hkey : a * (2 * (x / R) / (2 + x / R)) = 2 * x * (R + x) / (2 * R + x) := by
    rw [ha]; field_simp <;> ring
  have h2 : a * t ≥ 2 * x * (R + x) / (2 * R + x) := by
    rw [← hkey]
    exact mul_le_mul_of_nonneg_left hlb ha0.le
  have h3 : x - 2 * x * (R + x) / (2 * R + x) = -(x ^ 2 / (2 * R + x)) := by
    field_simp <;> ring
  have h4 : x ^ 2 / (2 * (R + x)) ≤ x ^ 2 / (2 * R + x) := by
    apply div_le_div_of_nonneg_left (sq_nonneg x) (by positivity) (by linarith)
  have h5 : -R + -(t * a) + R * (1 + x / R) = x - a * t := by
    field_simp <;> ring
  rw [h5]
  linarith
