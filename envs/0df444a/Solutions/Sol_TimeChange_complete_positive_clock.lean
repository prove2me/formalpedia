-- Prove2me | solution 1 for TimeChange.complete_positive_clock
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T14:58:10.608988+00:00
-- url     : https://prove2.me/submissions/e3ffccbc-62be-4480-8e13-22a04d19accc

import Mathlib.Dynamics.Flow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Order.Hom.Set
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Ring
open Set
open scoped Topology ContDiff
set_option maxHeartbeats 800000

theorem solution (r : ℝ → ℝ) (hr : Continuous r)
    (m : ℝ) (hm : 0 < m) (hbound : ∀ t, m ≤ r t) :
    ∃ clock : ℝ ≃o ℝ,
      clock 0 = 0 ∧
      (∀ t, HasDerivAt clock (r t) t) ∧
      (∀ a b : ℝ, a ≤ b → m * (b - a) ≤ clock b - clock a) ∧
      (∀ t, clock t = ∫ s in (0 : ℝ)..t, r s) := by
  let tau : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, r s
  have hd (t : ℝ) : HasDerivAt tau (r t) t :=
    intervalIntegral.integral_hasDerivAt_right (hr.intervalIntegrable 0 t)
      hr.aestronglyMeasurable.stronglyMeasurableAtFilter hr.continuousAt
  have hzero : tau 0 = 0 := by simp [tau]
  have hstrict : StrictMono tau :=
    strictMono_of_hasDerivAt_pos hd (fun t => lt_of_lt_of_le hm (hbound t))
  have hmono : Monotone (fun t => tau t - m * t) := by
    apply monotone_of_hasDerivAt_nonneg
      (fun t => (hd t).sub ((hasDerivAt_id t).const_mul m))
    intro t
    simpa only [Pi.zero_apply, mul_one] using sub_nonneg.mpr (hbound t)
  have hgrowth (a b : ℝ) (hab : a ≤ b) : m * (b - a) ≤ tau b - tau a := by
    have h := hmono hab
    dsimp at h
    nlinarith
  have hsurj : Function.Surjective tau := by
    intro z
    let a := min 0 (z / m)
    let b := max 0 (z / m)
    have ha : a ≤ 0 := min_le_left _ _
    have hb : 0 ≤ b := le_max_left _ _
    have hdiv : m * (z / m) = z := by field_simp [hm.ne']
    have hma : m * a ≤ z := by
      have h := mul_le_mul_of_nonneg_left (min_le_right 0 (z / m)) hm.le
      simpa only [hdiv] using h
    have hmb : z ≤ m * b := by
      have h := mul_le_mul_of_nonneg_left (le_max_right 0 (z / m)) hm.le
      simpa only [hdiv] using h
    have hza : tau a ≤ z := by
      have h := hgrowth a 0 ha
      rw [hzero] at h
      nlinarith
    have hzb : z ≤ tau b := by
      have h := hgrowth 0 b hb
      rw [hzero] at h
      nlinarith
    have hcont : Continuous tau := continuous_iff_continuousAt.mpr
      (fun t => (hd t).continuousAt)
    obtain ⟨t, _, ht⟩ := intermediate_value_Icc (ha.trans hb)
      hcont.continuousOn ⟨hza, hzb⟩
    exact ⟨t, ht⟩
  let clock := StrictMono.orderIsoOfSurjective tau hstrict hsurj
  refine ⟨clock, hzero, hd, hgrowth, ?_⟩
  intro t
  rfl
