-- Prove2me | solution 1 for WassVarReg.Boundary.boundaryGap_le
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T09:09:54.352213+00:00
-- url     : https://prove2.me/submissions/9cc5bb27-7288-4b68-ab90-3e6adc5081b7

import Mathlib
import Definitions.Def_WassVarReg_Boundary_Setting

set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ENNReal
open WassVarReg.Boundary

theorem pt_gap {Z : Type*} [MetricSpace Z] (ρ : ℝ) (hρ : 0 ≤ ρ) (D : Set Z) (z : Z) :
    WassVarReg.PInf.boundaryGap ρ D z ≤ ρ * nearIndicator ρ D z := by
  unfold WassVarReg.PInf.boundaryGap nearIndicator
  by_cases h : Metric.infEDist z D < ENNReal.ofReal ρ
  · rw [if_pos h, mul_one]
    calc (ENNReal.ofReal ρ - Metric.infEDist z D).toReal ≤ (ENNReal.ofReal ρ).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top tsub_le_self
      _ = ρ := ENNReal.toReal_ofReal hρ
  · rw [if_neg h, mul_zero]
    have : ENNReal.ofReal ρ - Metric.infEDist z D = 0 := tsub_eq_zero_of_le (not_lt.mp h)
    rw [this]; simp

theorem solution {Z : Type*} [MetricSpace Z]
    (n : ℕ) (hn : 0 < n) (ω : Fin n → Z) (ρ : ℝ) (hρ : 0 ≤ ρ) (D : Set Z) :
    (1 / (n : ℝ)) * ∑ i : Fin n, WassVarReg.PInf.boundaryGap ρ D (ω i) ≤
      ρ * ((1 / (n : ℝ)) * ∑ i : Fin n, nearIndicator ρ D (ω i)) := by
  have h : ∑ i : Fin n, WassVarReg.PInf.boundaryGap ρ D (ω i) ≤ ∑ i : Fin n, ρ * nearIndicator ρ D (ω i) :=
    Finset.sum_le_sum fun i _ => pt_gap ρ hρ D (ω i)
  rw [← Finset.mul_sum] at h
  have hn' : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
  calc (1 / (n : ℝ)) * ∑ i : Fin n, WassVarReg.PInf.boundaryGap ρ D (ω i)
      ≤ (1 / (n : ℝ)) * (ρ * ∑ i : Fin n, nearIndicator ρ D (ω i)) := mul_le_mul_of_nonneg_left h hn'
    _ = ρ * ((1 / (n : ℝ)) * ∑ i : Fin n, nearIndicator ρ D (ω i)) := by ring
