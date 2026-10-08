-- Prove2me | solution 1 for ParameterizedCalculus.smooth_unit_interval_integral
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-06T18:43:17.210897+00:00
-- url     : https://prove2.me/submissions/a3f343be-b072-4593-a82e-26af016ff685

import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith

open scoped ContDiff Convolution
open Set MeasureTheory

theorem solution {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (h : P → ℝ → ℝ) (hh : ContDiff ℝ ∞ (Function.uncurry h)) :
    ContDiff ℝ ∞ (fun p => ∫ s in (0 : ℝ)..1, h p s) := by
  let b : ContDiffBump (0 : ℝ) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  let g : P → ℝ → ℝ := fun p s => b s * h p (-s)
  have hg : ContDiff ℝ ∞ (Function.uncurry g) :=
    (b.contDiff.comp contDiff_snd).mul
      (hh.comp (contDiff_fst.prodMk contDiff_snd.neg))
  have hz : ∀ p s, p ∈ (univ : Set P) → s ∉ Metric.closedBall (0 : ℝ) 2 → g p s = 0 := by
    intro p s hp hs
    have hb : b s = 0 := by
      apply b.zero_of_le_dist
      have hn : 2 < dist s 0 := by simpa only [Metric.mem_closedBall, not_le] using hs
      exact hn.le
    simp [g, hb]
  have hc := contDiffOn_convolution_right_with_param_comp
    (μ := volume.restrict (Icc (0 : ℝ) 1))
    (ContinuousLinearMap.mul ℝ ℝ) (g := g) (s := univ)
    (v := fun _ : P => (0 : ℝ)) contDiffOn_const isOpen_univ
    (isCompact_closedBall (0 : ℝ) 2) hz
    ((integrable_const (1 : ℝ)).locallyIntegrable) hg.contDiffOn
  rw [contDiffOn_univ] at hc
  convert hc using 1
  funext p
  simp only [convolution, ContinuousLinearMap.mul_apply', one_mul, zero_sub]
  rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc]
  apply setIntegral_congr_fun measurableSet_Icc
  intro s hs
  have hb : b (-s) = 1 := by
    apply b.one_of_mem_closedBall
    simp only [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_neg]
    rw [abs_of_nonneg hs.1]
    exact hs.2
  simp [g, hb]
