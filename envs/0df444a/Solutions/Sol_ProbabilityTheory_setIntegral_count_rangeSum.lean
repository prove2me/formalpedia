-- Prove2me | solution 1 for ProbabilityTheory.setIntegral_count_rangeSum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T11:46:10.590557+00:00
-- url     : https://prove2.me/submissions/ea29f996-63ac-4e65-99c5-ed6131683407

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
import Theorems.Thm_ProbabilityTheory_integral_marksSum_eq

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Complex ComplexConjugate Set Filter Topology Finset ProbabilityTheory
open scoped NNReal ENNReal

theorem solution
    {Ω E : Type} [MeasurableSpace E] [MeasurableSpace Ω]
    {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E}
    {m : Measure E} [SigmaFinite m] [Nonempty E]
    {μ : Measure Ω} {k : ℕ} [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ)
    {g : E → ℝ} (hg : Measurable g)
    (hgi : Integrable g (m.restrict (prmPiece m k))) (j : ℕ) :
    ∫ ω in {ω | K k ω = j}, ∑ n ∈ Finset.range j, g (X k n ω) ∂μ
      = μ.real {ω | K k ω = j} *
        ((j : ℝ) * ∫ x, g x ∂(prmPieceLaw m k)) := by
  have hmeas : MeasurableSet {ω | K k ω = j} :=
    hd.measurable_count k (measurableSet_singleton j)
  set Xk : Ω → (ℕ → E) := fun ω n => X k n ω with hXk
  have hXk_meas : Measurable Xk :=
    measurable_pi_lambda _ fun n => hd.measurable_point k n
  set ψ : (ℕ → E) → ℝ := fun y => ∑ n ∈ Finset.range j, g (y n) with hψ
  have hψ_meas : Measurable ψ :=
    Finset.measurable_sum _ fun n _ => hg.comp (measurable_pi_apply n)
  have hcongr : ({ω | K k ω = j}).indicator (fun ω => ψ (Xk ω))
      = fun ω => (if K k ω = j then (1 : ℝ) else 0) * ψ (Xk ω) := by
    funext ω
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
    by_cases h : K k ω = j <;> simp [h]
  rw [← integral_indicator hmeas, hcongr,
    (hd.indepFun_count_marks k).integral_fun_comp_mul_comp
      (f := fun c : ℕ => if c = j then (1 : ℝ) else 0) (g := ψ)
      (hd.measurable_count k).aemeasurable hXk_meas.aemeasurable
      (measurable_of_countable _).aestronglyMeasurable hψ_meas.aestronglyMeasurable]
  have hfirst : ∫ ω, (if K k ω = j then (1 : ℝ) else 0) ∂μ =
      μ.real {ω | K k ω = j} := by
    have hrw : (fun ω => if K k ω = j then (1 : ℝ) else 0)
        = ({ω | K k ω = j}).indicator (fun _ => 1) := by
      funext ω
      by_cases h : K k ω = j <;> simp [Set.mem_setOf_eq, h]
    rw [hrw, integral_indicator_const (1 : ℝ) hmeas, smul_eq_mul, mul_one]
  rw [hfirst]
  congr 1
  exact ProbabilityTheory.integral_marksSum_eq hd hg hgi j
