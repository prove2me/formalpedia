-- Prove2me | solution 1 for PersuadeFly.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T21:15:14.376207+00:00
-- url     : https://prove2.me/submissions/83a7da37-f1be-445a-aab7-821a37db8f29

import Mathlib
import Definitions.Def_PersuadeFly_value
import Definitions.Def_PersuadeFly_IsMechanism
import Definitions.Def_PersuadeFly_l1Dist

open PersuadeFly in
theorem solution {Ω A : Type} [Fintype Ω] [Nontrivial Ω] [Fintype A] [Nontrivial A]
    (I : Instance Ω A) (μ1 μ2 : Ω → ℝ) (hμ1 : μ1 ∈ stdSimplex ℝ Ω) (hμ2 : μ2 ∈ stdSimplex ℝ Ω)
    (σ : Ω → A → ℝ) (hσ : IsMechanism σ) :
    |value I μ1 σ - value I μ2 σ| ≤ 1 / 2 * l1Dist μ1 μ2 := by
  obtain ⟨f, hfdef⟩ : ∃ f : Ω → ℝ, f = fun ω => ∑ a, σ ω a * I.v ω a := ⟨_, rfl⟩
  have hf : ∀ ω, 0 ≤ f ω ∧ f ω ≤ 1 := by
    intro ω
    rw [hfdef]
    constructor
    · exact Finset.sum_nonneg (fun a _ => mul_nonneg ((hσ ω).1 a) (I.v_nonneg ω a))
    · calc ∑ a, σ ω a * I.v ω a ≤ ∑ a, σ ω a := by
            apply Finset.sum_le_sum
            intro a _
            exact mul_le_of_le_one_right ((hσ ω).1 a) (I.v_le_one ω a)
        _ = 1 := (hσ ω).2
  have hv : ∀ μ : Ω → ℝ, value I μ σ = ∑ ω, μ ω * f ω := by
    intro μ
    unfold value
    rw [hfdef]
    apply Finset.sum_congr rfl
    intro ω _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  have hsum : ∑ ω, (μ1 ω - μ2 ω) = 0 := by
    rw [Finset.sum_sub_distrib, hμ1.2, hμ2.2, sub_self]
  have hdiff : value I μ1 σ - value I μ2 σ = ∑ ω, (μ1 ω - μ2 ω) * (f ω - 1 / 2) := by
    have e : ∑ ω, (μ1 ω - μ2 ω) * (f ω - 1 / 2) =
        ∑ ω, (μ1 ω * f ω - μ2 ω * f ω) - 1 / 2 * ∑ ω, (μ1 ω - μ2 ω) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro ω _
      ring
    rw [e, hsum, hv, hv, Finset.sum_sub_distrib]
    ring
  rw [hdiff]
  calc |∑ ω, (μ1 ω - μ2 ω) * (f ω - 1 / 2)| ≤ ∑ ω, |(μ1 ω - μ2 ω) * (f ω - 1 / 2)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ ω, |μ1 ω - μ2 ω| * (1 / 2) := by
        apply Finset.sum_le_sum
        intro ω _
        rw [abs_mul]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        rw [abs_le]
        constructor <;> linarith [(hf ω).1, (hf ω).2]
    _ = 1 / 2 * l1Dist μ1 μ2 := by
        unfold l1Dist
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ω _
        ring
