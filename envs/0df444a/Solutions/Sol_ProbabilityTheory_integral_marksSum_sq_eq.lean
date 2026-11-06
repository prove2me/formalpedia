-- Prove2me | solution 1 for ProbabilityTheory.integral_marksSum_sq_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T12:09:25.050095+00:00
-- url     : https://prove2.me/submissions/1cab2ad2-7b0f-4fad-9d01-1d31bfb357ec

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Independence.Basic
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
import Theorems.Thm_ProbabilityTheory_integrable_prmPieceLaw

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
    (hd : IsPoissonPointFamily K X m μ) {f : E → ℝ}
    (hf : Measurable f)
    (hfi : Integrable f (m.restrict (prmPiece m k)))
    (hfi2 : Integrable (fun x => f x ^ 2) (m.restrict (prmPiece m k)))
    (j : ℕ) :
    ∫ ω, (∑ n ∈ Finset.range j, f (X k n ω)) ^ 2 ∂μ =
      (j : ℝ) * (∫ x, f x ^ 2 ∂(prmPieceLaw m k)) +
      (j : ℝ) * ((j : ℝ) - 1) * (∫ x, f x ∂(prmPieceLaw m k)) ^ 2 := by
  classical
  set A := ∫ x, f x ^ 2 ∂(prmPieceLaw m k) with hA
  set B := ∫ x, f x ∂(prmPieceLaw m k) with hB
  have hf2m : Measurable (fun x => f x ^ 2) := hf.pow_const 2
  have hInt_f : ∀ n, Integrable (fun ω => f (X k n ω)) μ := by
    intro n
    have hI : Integrable f (μ.map (X k n)) := by
      rw [(hd.law_point k n).map_eq]
      exact ProbabilityTheory.integrable_prmPieceLaw hf hfi
    exact hI.comp_measurable (hd.measurable_point k n)
  have hInt_f2 : ∀ n, Integrable (fun ω => f (X k n ω) ^ 2) μ := by
    intro n
    have hI : Integrable (fun x => f x ^ 2) (μ.map (X k n)) := by
      rw [(hd.law_point k n).map_eq]
      exact ProbabilityTheory.integrable_prmPieceLaw hf2m hfi2
    exact hI.comp_measurable (hd.measurable_point k n)
  have heach_f : ∀ n, ∫ ω, f (X k n ω) ∂μ = B := by
    intro n
    rw [hB, ← (hd.law_point k n).map_eq,
      integral_map (hd.measurable_point k n).aemeasurable hf.aestronglyMeasurable]
  have heach_f2 : ∀ n, ∫ ω, f (X k n ω) ^ 2 ∂μ = A := by
    intro n
    rw [hA, ← (hd.law_point k n).map_eq,
      integral_map (hd.measurable_point k n).aemeasurable hf2m.aestronglyMeasurable]
  have hindep : ∀ n n', n ≠ n' →
      IndepFun (fun ω => f (X k n ω)) (fun ω => f (X k n' ω)) μ :=
    fun n n' h => ((hd.iIndepFun_point_piece k).indepFun h).comp hf hf
  have hprod : ∀ n n', Integrable (fun ω => f (X k n ω) * f (X k n' ω)) μ := by
    intro n n'
    by_cases h : n = n'
    · subst h
      simpa [pow_two] using hInt_f2 n
    · exact (hindep n n' h).integrable_mul (hInt_f n) (hInt_f n')
  have hprod_val : ∀ n n', ∫ ω, f (X k n ω) * f (X k n' ω) ∂μ =
      if n = n' then A else B ^ 2 := by
    intro n n'
    by_cases h : n = n'
    · subst h
      rw [if_pos rfl]
      simp_rw [← pow_two]
      exact heach_f2 n
    · rw [if_neg h, (hindep n n' h).integral_fun_mul_eq_mul_integral
        (hInt_f n).aestronglyMeasurable (hInt_f n').aestronglyMeasurable,
        heach_f n, heach_f n', ← pow_two]
  have hexp : (fun ω => (∑ n ∈ Finset.range j, f (X k n ω)) ^ 2) =
      fun ω => ∑ n ∈ Finset.range j, ∑ n' ∈ Finset.range j,
        f (X k n ω) * f (X k n' ω) := by
    funext ω
    rw [pow_two, Finset.sum_mul_sum]
  rw [hexp, integral_finsetSum _ fun n _ =>
    integrable_finsetSum _ fun n' _ => hprod n n']
  have hinner : ∀ n, ∫ ω, ∑ n' ∈ Finset.range j,
      f (X k n ω) * f (X k n' ω) ∂μ =
      ∑ n' ∈ Finset.range j, (if n = n' then A else B ^ 2) := by
    intro n
    rw [integral_finsetSum _ fun n' _ => hprod n n']
    exact Finset.sum_congr rfl fun n' _ => hprod_val n n'
  simp_rw [hinner]
  have hin : ∀ n ∈ Finset.range j,
      (∑ n' ∈ Finset.range j, (if n = n' then A else B ^ 2)) =
        A + ((j : ℝ) - 1) * B ^ 2 := by
    intro n hn
    have hrw : ∀ n', (if n = n' then A else B ^ 2) =
        B ^ 2 + (if n = n' then (A - B ^ 2) else 0) := by
      intro n'
      split_ifs <;> ring
    simp_rw [hrw]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, Finset.sum_ite_eq (Finset.range j) n
      (fun _ => A - B ^ 2), if_pos hn]
    ring
  rw [Finset.sum_congr rfl hin, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring
