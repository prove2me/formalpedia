-- Prove2me | solution 1 for RealPoisson.interval_arctan_mass_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-05T00:30:16.272732+00:00
-- url     : https://prove2.me/submissions/49c4217f-d52b-4612-97b2-b0f0f5158fd2

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.NormNum

open MeasureTheory Filter Set
open scoped Topology

namespace HerglotzStieltjes

noncomputable def intervalKernel (a b ε x : ℝ) : ℝ :=
  (Real.arctan ((b - x) / ε) - Real.arctan ((a - x) / ε)) / Real.pi
theorem intervalKernel_mem_Icc (a b ε x : ℝ) (hab : a ≤ b) (hε : 0 < ε) :
    intervalKernel a b ε x ∈ Icc 0 1 := by
  have hm := Real.arctan_strictMono.monotone
    (div_le_div_of_nonneg_right (sub_le_sub_right hab x) hε.le)
  have hu := Real.arctan_lt_pi_div_two ((b - x) / ε)
  have hl := Real.neg_pi_div_two_lt_arctan ((a - x) / ε)
  constructor
  · exact div_nonneg (sub_nonneg.mpr hm) Real.pi_pos.le
  · apply (div_le_one Real.pi_pos).mpr
    linarith

theorem arctan_div_tendsto_pos (c : ℝ) (hc : 0 < c) :
    Tendsto (fun ε : ℝ => Real.arctan (c / ε)) (𝓝[>] 0) (𝓝 (Real.pi / 2)) := by
  apply Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds |>.comp
  change Tendsto (fun ε : ℝ => c * ε⁻¹) (𝓝[>] 0) atTop
  exact tendsto_inv_nhdsGT_zero.const_mul_atTop hc

theorem arctan_div_tendsto_neg (c : ℝ) (hc : c < 0) :
    Tendsto (fun ε : ℝ => Real.arctan (c / ε)) (𝓝[>] 0) (𝓝 (-(Real.pi / 2))) := by
  have h := (arctan_div_tendsto_pos (-c) (neg_pos.mpr hc)).neg
  simpa [neg_div, Real.arctan_neg] using h

theorem intervalKernel_tendsto (a b x : ℝ) (hab : a < b) :
    Tendsto (fun ε : ℝ => intervalKernel a b ε x) (𝓝[>] 0)
      (𝓝 (((Ioo a b).indicator (fun _ => (1 : ℝ)) x +
        (Icc a b).indicator (fun _ => (1 : ℝ)) x) / 2)) := by
  unfold intervalKernel
  rcases lt_trichotomy x a with hxa | rfl | hax
  · have h₁ := arctan_div_tendsto_pos (b-x) (by linarith)
    have h₂ := arctan_div_tendsto_pos (a-x) (sub_pos.mpr hxa)
    simpa [indicator_of_notMem, show x ∉ Ioo a b from fun h => (not_lt.mpr hxa.le) h.1,
      show x ∉ Icc a b from fun h => (not_le.mpr hxa) h.1] using
      (h₁.sub h₂).div_const Real.pi
  · have h₁ := arctan_div_tendsto_pos (b-x) (sub_pos.mpr hab)
    have h₂ : Tendsto (fun ε : ℝ => Real.arctan ((x-x)/ε)) (𝓝[>] 0) (𝓝 0) := by simp
    convert (h₁.sub h₂).div_const Real.pi using 1
    simp [hab.le]
    field_simp
  · rcases lt_trichotomy x b with hxb | rfl | hbx
    · have h₁ := arctan_div_tendsto_pos (b-x) (sub_pos.mpr hxb)
      have h₂ := arctan_div_tendsto_neg (a-x) (sub_neg.mpr hax)
      convert (h₁.sub h₂).div_const Real.pi using 1
      simp [hax, hxb, hax.le, hxb.le, Real.pi_ne_zero]
    · have h₁ : Tendsto (fun ε : ℝ => Real.arctan ((x-x)/ε)) (𝓝[>] 0) (𝓝 0) := by simp
      have h₂ := arctan_div_tendsto_neg (a-x) (sub_neg.mpr hab)
      convert (h₁.sub h₂).div_const Real.pi using 1
      simp [hab.le]
      field_simp
    · have h₁ := arctan_div_tendsto_neg (b-x) (sub_neg.mpr hbx)
      have h₂ := arctan_div_tendsto_neg (a-x) (by linarith)
      simpa [indicator_of_notMem,
        show x ∉ Ioo a b from fun h => (not_lt.mpr hbx.le) h.2,
        show x ∉ Icc a b from fun h => (not_le.mpr hbx) h.2] using
        (h₁.sub h₂).div_const Real.pi

theorem integral_intervalKernel_tendsto (μ : Measure ℝ) [IsFiniteMeasure μ]
    (a b : ℝ) (hab : a < b) :
    Tendsto (fun ε : ℝ => ∫ x : ℝ, intervalKernel a b ε x ∂μ) (𝓝[>] 0)
      (𝓝 (((μ (Ioo a b)).toReal + (μ (Icc a b)).toReal) / 2)) := by
  have h := tendsto_integral_filter_of_dominated_convergence (μ := μ)
    (F := fun ε x => intervalKernel a b ε x)
    (f := fun x => ((Ioo a b).indicator (fun _ => (1 : ℝ)) x +
      (Icc a b).indicator (fun _ => (1 : ℝ)) x) / 2)
    (fun _ => (1 : ℝ))
    (Eventually.of_forall fun ε => by unfold intervalKernel; fun_prop)
    (by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      apply Eventually.of_forall
      intro x
      rw [Real.norm_eq_abs, abs_of_nonneg (intervalKernel_mem_Icc a b ε x hab.le hε).1]
      exact (intervalKernel_mem_Icc a b ε x hab.le hε).2)
    (integrable_const 1)
    (Eventually.of_forall fun x => intervalKernel_tendsto a b x hab)
  convert h using 1
  rw [integral_div, integral_add]
  · simp [integral_indicator measurableSet_Ioo, integral_indicator measurableSet_Icc,
      measureReal_def]
  · exact (integrable_const 1).indicator measurableSet_Ioo
  · exact (integrable_const 1).indicator measurableSet_Icc

end HerglotzStieltjes

open HerglotzStieltjes

theorem solution (μ : Measure ℝ) [IsFiniteMeasure μ]
    (a b : ℝ) (hab : a < b) :
    Tendsto (fun ε : ℝ => ∫ x : ℝ, (Real.arctan ((b - x) / ε) - Real.arctan ((a - x) / ε)) / Real.pi ∂μ) (𝓝[>] 0)
      (𝓝 (((μ (Ioo a b)).toReal + (μ (Icc a b)).toReal) / 2)) := by
  exact integral_intervalKernel_tendsto μ a b hab

