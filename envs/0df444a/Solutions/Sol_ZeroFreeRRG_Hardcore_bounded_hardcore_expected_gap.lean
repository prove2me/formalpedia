-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.bounded_hardcore_expected_gap
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T07:38:25.12183+00:00
-- url     : https://prove2.me/submissions/a0361082-5d17-4f4d-bd17-ccdbb69c2a6e

import Theorems.Thm_ZeroFreeRRG_Hardcore_hardcore_expected_supermodular_gap
import Mathlib
set_option autoImplicit false
open scoped Classical BigOperators
open MeasureTheory Set ZeroFreeRRG.Hardcore

theorem solution (d : ℕ) (hd : 2 ≤ d) (θ C : ℝ) (hθ : 0 < θ) (hC : 0 ≤ C)
    (π : Measure (ℝ × ℝ)) [IsProbabilityMeasure π]
    (hbound : ∀ᵐ p ∂π, 0 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ C)
    (hs : 0 < π {p | p.1 < p.2}) (hp : 0 < π {p | 0 < p.1}) :
    let g := fun (xs : Fin d → ℝ × ℝ) (S : Finset (Fin d)) =>
        Real.log (1+θ*∏ a, if a ∈ S then (xs a).2 else (xs a).1)
    0 < ∫ xs, g xs Finset.univ - g xs ∅ - ∑ i, (g xs {i}-g xs ∅)
      ∂(Measure.pi fun _ : Fin d => π) := by
  classical
  dsimp only
  let μ := Measure.pi fun _ : Fin d => π
  let g := fun (xs : Fin d → ℝ × ℝ) (S : Finset (Fin d)) =>
    Real.log (1+θ*∏ a, if a ∈ S then (xs a).2 else (xs a).1)
  have hgood : ∀ᵐ xs ∂μ, ∀ a, 0 ≤ (xs a).1 ∧ (xs a).1 ≤ (xs a).2 ∧ (xs a).2 ≤ C := by
    apply Measure.ae_pi_le_pi
    exact Filter.eventually_pi (fun _ : Fin d => hbound)
  have hlogcont : ContinuousOn Real.log (Icc (1:ℝ) (1+θ*C^d)) := by
    apply Real.continuousOn_log.mono
    intro x hx
    simp only [mem_Icc,mem_compl_iff,mem_singleton_iff] at *
    linarith [hx.1]
  obtain ⟨B,hB⟩ := (isCompact_Icc : IsCompact (Icc (1:ℝ) (1+θ*C^d))).exists_bound_of_continuousOn hlogcont
  have hgi (S : Finset (Fin d)) : Integrable (fun xs => g xs S) μ := by
    have hm : Measurable (fun xs : Fin d → ℝ × ℝ => g xs S) := by
      dsimp [g]
      have hprod : Measurable (fun xs : Fin d → ℝ × ℝ =>
          ∏ a, if a ∈ S then (xs a).2 else (xs a).1) := by
        apply Finset.measurable_prod
        intro a ha
        by_cases h : a ∈ S
        · simp only [h,if_true]
          exact measurable_snd.comp (measurable_pi_apply a)
        · simp only [h,if_false]
          exact measurable_fst.comp (measurable_pi_apply a)
      exact (measurable_const.add (measurable_const.mul hprod)).log
    apply Integrable.of_bound hm.aestronglyMeasurable B
    filter_upwards [hgood] with xs hx
    have hp0 (a : Fin d) : 0 ≤ (if a ∈ S then (xs a).2 else (xs a).1) := by
      split_ifs <;> linarith [(hx a).1,(hx a).2.1]
    have hpC (a : Fin d) : (if a ∈ S then (xs a).2 else (xs a).1) ≤ C := by
      split_ifs <;> linarith [(hx a).2.1,(hx a).2.2]
    have hprod0 : 0 ≤ ∏ a : Fin d, (if a ∈ S then (xs a).2 else (xs a).1) :=
      Finset.prod_nonneg (fun a _ => hp0 a)
    have hprodC : (∏ a : Fin d, (if a ∈ S then (xs a).2 else (xs a).1)) ≤ C^d := by
      calc
        _ ≤ ∏ _a : Fin d, C := Finset.prod_le_prod (fun a _ => hp0 a) (fun a _ => hpC a)
        _ = _ := by simp
    have harg : 1+θ*∏ a : Fin d, (if a ∈ S then (xs a).2 else (xs a).1) ∈ Icc (1:ℝ) (1+θ*C^d) := by
      constructor
      · nlinarith [mul_nonneg hθ.le hprod0]
      · nlinarith [mul_nonneg hθ.le (sub_nonneg.mpr hprodC)]
    exact hB _ harg
  have hI : Integrable (fun xs => g xs Finset.univ - g xs ∅ - ∑ i, (g xs {i}-g xs ∅)) μ := by
    apply (hgi Finset.univ).sub (hgi ∅) |>.sub
    apply integrable_finsetSum
    intro i hi
    exact (hgi {i}).sub (hgi ∅)
  have horder : ∀ᵐ p ∂π, 0 ≤ p.1 ∧ p.1 ≤ p.2 := by
    filter_upwards [hbound] with p hp'
    exact ⟨hp'.1,hp'.2.1⟩
  exact hardcore_expected_supermodular_gap d hd θ hθ π horder hs hp hI
