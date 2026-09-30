-- Prove2me | solution 1 for TranscendenceTheory.exists_entire_monomial_regularization
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-07T13:40:14.959511+00:00
-- url     : https://prove2.me/submissions/aa626d78-9ea9-4e5c-a6b5-f0d3a0a02c1b

import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

noncomputable section

open Finset Set


/-- Entire extension of a finite sum with a common weighted pole budget,
with a bound uniform in the radius and in the supplied entire factors. -/
theorem solution
    {ι κ : Type} [Fintype ι] [Fintype κ]
    (U : Set ℂ) (σ : ℂ → ℂ) (φ ψ : κ → ℂ → ℂ)
    (hσ : AnalyticOnNhd ℂ σ univ)
    (hψ : ∀ j, AnalyticOnNhd ℂ (ψ j) univ)
    (w : κ → ℕ) (hw : ∀ j, 1 ≤ w j)
    (hrel : ∀ z ∈ U, ∀ j, ψ j z = σ z ^ w j * φ j z)
    (v : ℂ) (c : ι → ℂ) (l : ι → ℕ) (e : ι → κ → ℕ)
    (D K : ℕ) (hl : ∀ i, l i ≤ D) (he : ∀ i, ∑ j, w j * e i j ≤ K) :
    ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G univ ∧
      (∀ z ∈ U, G z = σ z ^ K * ∑ i, c i * (z + v) ^ l i * ∏ j, φ j z ^ e i j) ∧
      ∀ R B : ℝ, 1 ≤ B →
        (∀ z : ℂ, ‖z‖ ≤ R → ‖σ z‖ ≤ B ∧ ∀ j, ‖ψ j z‖ ≤ B) →
        ∀ z : ℂ, ‖z‖ ≤ R →
          ‖G z‖ ≤ (∑ i, ‖c i‖) * (max 1 (R + ‖v‖)) ^ D * B ^ K := by
  classical
  let G : ℂ → ℂ := fun z => ∑ i, c i * (z + v) ^ l i *
    (σ z ^ (K - ∑ j, w j * e i j) * ∏ j, ψ j z ^ e i j)
  refine ⟨G, ?_, ?_, ?_⟩
  · intro z _
    have hprod (i : ι) : AnalyticAt ℂ (fun z => ∏ j, ψ j z ^ e i j) z := by
      simpa only [Finset.prod_fn, Pi.pow_apply] using
        (Finset.analyticAt_prod univ fun j _ => (hψ j z trivial).pow (e i j))
    have hterm (i : ι) : AnalyticAt ℂ (fun z => c i * (z + v) ^ l i *
        (σ z ^ (K - ∑ j, w j * e i j) * ∏ j, ψ j z ^ e i j)) z :=
      (analyticAt_const.mul ((analyticAt_id.add analyticAt_const).pow (l i))).mul
        (((hσ z trivial).pow _).mul (hprod i))
    simpa only [G, Finset.sum_fn] using
      (Finset.analyticAt_sum univ fun i _ => hterm i)
  · intro z hz
    dsimp only [G]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hfactor : σ z ^ (K - ∑ j, w j * e i j) * ∏ j, ψ j z ^ e i j =
        σ z ^ K * ∏ j, φ j z ^ e i j := by
      simp only [hrel z hz, mul_pow, ← pow_mul, Finset.prod_mul_distrib,
        Finset.prod_pow_eq_pow_sum]
      rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel (he i)]
    rw [hfactor]
    ring
  · intro R B hB hbound z hz
    have hB0 : 0 ≤ B := le_trans (by norm_num) hB
    have hX : 1 ≤ max 1 (R + ‖v‖) := le_max_left _ _
    have hX0 : 0 ≤ max 1 (R + ‖v‖) := le_trans (by norm_num) hX
    have hzv : ‖z + v‖ ≤ max 1 (R + ‖v‖) :=
      (norm_add_le z v).trans ((add_le_add hz (le_refl ‖v‖)).trans (le_max_right _ _))
    have hterm (i : ι) :
        ‖c i * (z + v) ^ l i *
          (σ z ^ (K - ∑ j, w j * e i j) * ∏ j, ψ j z ^ e i j)‖ ≤
        ‖c i‖ * (max 1 (R + ‖v‖)) ^ D * B ^ K := by
      have hsum : ∑ j, e i j ≤ ∑ j, w j * e i j := by
        apply Finset.sum_le_sum
        intro j _
        simpa using Nat.mul_le_mul_right (e i j) (hw j)
      have hprod : (∏ j, ‖ψ j z‖ ^ e i j) ≤ B ^ (∑ j, e i j) := by
        rw [← Finset.prod_pow_eq_pow_sum]
        exact Finset.prod_le_prod (fun j _ => pow_nonneg (norm_nonneg _) _)
          (fun j _ => pow_le_pow_left₀ (norm_nonneg _) ((hbound z hz).2 j) _)
      have hpole : ‖σ z‖ ^ (K - ∑ j, w j * e i j) *
          (∏ j, ‖ψ j z‖ ^ e i j) ≤ B ^ K := by
        calc
          _ ≤ B ^ (K - ∑ j, w j * e i j) * B ^ (∑ j, e i j) :=
            mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hbound z hz).1 _)
              hprod (by positivity) (by positivity)
          _ = B ^ ((K - ∑ j, w j * e i j) + ∑ j, e i j) := (pow_add _ _ _).symm
          _ ≤ B ^ K := pow_le_pow_right₀ hB (by have := he i; omega)
      simp only [norm_mul, norm_pow, norm_prod]
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left
          ((pow_le_pow_left₀ (norm_nonneg _) hzv _).trans
            (pow_le_pow_right₀ hX (hl i))) (norm_nonneg _))
        hpole (by positivity) (by positivity)
    calc
      ‖G z‖ ≤ ∑ i, ‖c i * (z + v) ^ l i *
          (σ z ^ (K - ∑ j, w j * e i j) * ∏ j, ψ j z ^ e i j)‖ := norm_sum_le _ _
      _ ≤ ∑ i, ‖c i‖ * (max 1 (R + ‖v‖)) ^ D * B ^ K :=
        Finset.sum_le_sum fun i _ => hterm i
      _ = _ := by rw [Finset.sum_mul, Finset.sum_mul]

