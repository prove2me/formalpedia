-- Prove2me | solution 1 for ProbabilityTheory.setIntegral_count_marksFun
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T12:02:29.959192+00:00
-- url     : https://prove2.me/submissions/4e2d482a-84d9-45da-9473-dc0411b261f8

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

theorem solution
    {Ω E : Type} [MeasurableSpace E] [MeasurableSpace Ω]
    {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E}
    {m : Measure E} [SigmaFinite m] [Nonempty E]
    {μ : Measure Ω} {k : ℕ} [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) (j : ℕ)
    {ψ : (ℕ → E) → ℝ} (hψ : Measurable ψ) :
    ∫ ω in {ω | K k ω = j}, ψ (fun n => X k n ω) ∂μ =
      μ.real {ω | K k ω = j} * ∫ ω, ψ (fun n => X k n ω) ∂μ := by
  have hmeas : MeasurableSet {ω | K k ω = j} :=
    hd.measurable_count k (measurableSet_singleton j)
  set Xk : Ω → (ℕ → E) := fun ω n => X k n ω with hXk
  have hXk_meas : Measurable Xk :=
    measurable_pi_lambda _ fun n => hd.measurable_point k n
  have hcongr : ({ω | K k ω = j}).indicator (fun ω => ψ (Xk ω)) =
      fun ω => (if K k ω = j then (1 : ℝ) else 0) * ψ (Xk ω) := by
    funext ω
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
    by_cases h : K k ω = j <;> simp [h]
  rw [← integral_indicator hmeas, hcongr,
    (hd.indepFun_count_marks k).integral_fun_comp_mul_comp
      (f := fun c : ℕ => if c = j then (1 : ℝ) else 0) (g := ψ)
      (hd.measurable_count k).aemeasurable hXk_meas.aemeasurable
      (measurable_of_countable _).aestronglyMeasurable hψ.aestronglyMeasurable]
  have hfirst : ∫ ω, (if K k ω = j then (1 : ℝ) else 0) ∂μ =
      μ.real {ω | K k ω = j} := by
    have hrw : (fun ω => if K k ω = j then (1 : ℝ) else 0) =
        ({ω | K k ω = j}).indicator (fun _ => 1) := by
      funext ω
      by_cases h : K k ω = j <;> simp [Set.mem_setOf_eq, h]
    rw [hrw, integral_indicator_const (1 : ℝ) hmeas, smul_eq_mul, mul_one]
  rw [hfirst]
