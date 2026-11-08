-- Prove2me | solution 1 for PersuadeFly.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T20:13:10.802499+00:00
-- url     : https://prove2.me/submissions/bd69abb2-f7ac-40e8-a6b2-3bbd474d3694

import Mathlib
import Definitions.Def_PersuadeFly_gap
import Definitions.Def_PersuadeFly_ball1

open PersuadeFly in
theorem solution {Ω A : Type} [Fintype Ω] [Nontrivial Ω] [Fintype A] [Nontrivial A]
    (I : Instance Ω A) (μ1 μ2 : Ω → ℝ) (hμ1 : μ1 ∈ stdSimplex ℝ Ω) (hμ2 : μ2 ∈ stdSimplex ℝ Ω) :
    opt I μ1 - opt I μ2 ≤ gap I μ1 (ball1 μ1 (l1Dist μ1 μ2)) + 1 / 2 * l1Dist μ1 μ2 := by
  have hf : ∀ σ : Ω → A → ℝ, IsMechanism σ → ∀ ω,
      0 ≤ ∑ a, σ ω a * I.v ω a ∧ ∑ a, σ ω a * I.v ω a ≤ 1 := by
    intro σ hσ ω
    obtain ⟨hnn, hsum⟩ := hσ ω
    constructor
    · exact Finset.sum_nonneg (fun a _ => mul_nonneg (hnn a) (I.v_nonneg ω a))
    · calc ∑ a, σ ω a * I.v ω a ≤ ∑ a, σ ω a :=
            Finset.sum_le_sum (fun a _ => mul_le_of_le_one_right (hnn a) (I.v_le_one ω a))
        _ = 1 := hsum
  have hvalf : ∀ (μ : Ω → ℝ) (σ : Ω → A → ℝ),
      value I μ σ = ∑ ω, μ ω * ∑ a, σ ω a * I.v ω a := by
    intro μ σ
    unfold value
    refine Finset.sum_congr rfl (fun ω _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    ring
  have hval_nonneg : ∀ μ ∈ stdSimplex ℝ Ω, ∀ σ : Ω → A → ℝ, IsMechanism σ →
      0 ≤ value I μ σ := by
    intro μ hμ σ hσ
    rw [hvalf]
    exact Finset.sum_nonneg (fun ω _ => mul_nonneg (hμ.1 ω) (hf σ hσ ω).1)
  have hval_le : ∀ μ ∈ stdSimplex ℝ Ω, ∀ σ : Ω → A → ℝ, IsMechanism σ →
      value I μ σ ≤ 1 := by
    intro μ hμ σ hσ
    rw [hvalf]
    calc ∑ ω, μ ω * ∑ a, σ ω a * I.v ω a ≤ ∑ ω, μ ω :=
          Finset.sum_le_sum (fun ω _ => mul_le_of_le_one_right (hμ.1 ω) (hf σ hσ ω).2)
      _ = 1 := hμ.2
  have hopt_nonneg : 0 ≤ opt I μ2 := by
    unfold opt
    apply Real.sSup_nonneg
    rintro _ ⟨σ, hσ, rfl⟩
    exact hval_nonneg μ2 hμ2 σ hσ.1
  have hbdd : BddAbove (value I μ2 '' pers I μ2) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨σ, hσ, rfl⟩
    exact hval_le μ2 hμ2 σ hσ.1
  have hd0 : 0 ≤ l1Dist μ1 μ2 := Finset.sum_nonneg (fun ω _ => abs_nonneg _)
  have hmem : μ2 ∈ ball1 μ1 (l1Dist μ1 μ2) := by
    refine ⟨hμ2, le_of_eq ?_⟩
    unfold l1Dist
    exact Finset.sum_congr rfl (fun ω _ => abs_sub_comm _ _)
  have hdiff : ∀ σ : Ω → A → ℝ, IsMechanism σ →
      value I μ1 σ ≤ value I μ2 σ + 1 / 2 * l1Dist μ1 μ2 := by
    intro σ hσ
    rw [hvalf, hvalf]
    have key : ∀ ω, μ1 ω * ∑ a, σ ω a * I.v ω a ≤
        μ2 ω * ∑ a, σ ω a * I.v ω a + (μ1 ω - μ2 ω) * (1 / 2) + 1 / 2 * |μ1 ω - μ2 ω| := by
      intro ω
      have hF := hf σ hσ ω
      have h1 : |∑ a, σ ω a * I.v ω a - 1 / 2| ≤ 1 / 2 :=
        abs_le.mpr ⟨by linarith [hF.1], by linarith [hF.2]⟩
      have h2 : (μ1 ω - μ2 ω) * (∑ a, σ ω a * I.v ω a - 1 / 2) ≤ |μ1 ω - μ2 ω| * (1 / 2) := by
        refine (le_abs_self _).trans ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      nlinarith
    have hsum0 : ∑ ω, (μ1 ω - μ2 ω) * (1 / 2) = 0 := by
      rw [← Finset.sum_mul, Finset.sum_sub_distrib, hμ1.2, hμ2.2]
      ring
    calc ∑ ω, μ1 ω * ∑ a, σ ω a * I.v ω a
        ≤ ∑ ω, (μ2 ω * ∑ a, σ ω a * I.v ω a + (μ1 ω - μ2 ω) * (1 / 2) +
            1 / 2 * |μ1 ω - μ2 ω|) := Finset.sum_le_sum (fun ω _ => key ω)
      _ = ∑ ω, μ2 ω * ∑ a, σ ω a * I.v ω a + 1 / 2 * l1Dist μ1 μ2 := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hsum0, ← Finset.mul_sum]
          unfold l1Dist
          ring
  unfold gap
  suffices H : sSup (value I μ1 '' persSet I (ball1 μ1 (l1Dist μ1 μ2))) ≤
      opt I μ2 + 1 / 2 * l1Dist μ1 μ2 by linarith
  rcases (value I μ1 '' persSet I (ball1 μ1 (l1Dist μ1 μ2))).eq_empty_or_nonempty with he | hne
  · rw [he, Real.sSup_empty]
    linarith
  · apply csSup_le hne
    rintro _ ⟨σ, hσ, rfl⟩
    have h2 : σ ∈ pers I μ2 := hσ.2 μ2 hmem
    have h3 : value I μ2 σ ≤ opt I μ2 := le_csSup hbdd ⟨σ, h2, rfl⟩
    linarith [hdiff σ hσ.1]
