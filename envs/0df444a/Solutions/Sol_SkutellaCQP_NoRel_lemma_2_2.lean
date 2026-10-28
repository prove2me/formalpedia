-- Prove2me | solution 1 for SkutellaCQP.NoRel.lemma_2_2
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-28T20:27:22.939857+00:00
-- url     : https://prove2.me/submissions/59f05932-0e2c-4db6-8c55-d79ced5088cd

import Mathlib
import Definitions.Def_SkutellaCQP_NoRel_Setting

open SkutellaCQP.NoRel
open Finset Matrix

theorem solution {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ)
    (hp : ∀ i j, 0 < p i j) (hw : ∀ j, 0 ≤ w j)
    (μ : (Fin n → Fin m) → ℝ) (hμ0 : ∀ σ, 0 ≤ μ σ) (hμ1 : ∑ σ, μ σ = 1) (j : Fin n) :
    E μ (fun σ => SkutellaCQP.NoRel.compl p w σ j) =
      ∑ i, ((∑ σ ∈ univ.filter (fun σ : Fin n → Fin m => σ j = i), μ σ) * p i j +
        ∑ k ∈ univ.filter (fun k => prec p w i k j),
          (∑ σ ∈ univ.filter (fun σ : Fin n → Fin m => σ j = i ∧ σ k = i), μ σ) * p i k) := by
  dsimp only [E, SkutellaCQP.NoRel.compl]
  have h1 :
      (∑ σ : Fin n → Fin m,
          μ σ * (p (σ j) j + ∑ k ∈ univ.filter (fun k => prec p w (σ j) k j ∧ σ k = σ j), p (σ j) k)) =
        ∑ σ : Fin n → Fin m, ∑ i : Fin m,
          if σ j = i then
            μ σ * (p i j + ∑ k ∈ univ.filter (fun k => prec p w i k j), if σ k = i then p i k else 0)
          else 0 := by
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.sum_ite_eq univ (σ j)]
    simp only [Finset.mem_univ, ↓reduceIte]
    congr 2
    rw [Finset.sum_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases h1 : prec p w (σ j) k j <;> by_cases h2 : σ k = σ j <;> simp [h1, h2]
  rw [h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h2 :
      (∑ σ : Fin n → Fin m,
          if σ j = i then
            μ σ * (p i j + ∑ k ∈ univ.filter (fun k => prec p w i k j), if σ k = i then p i k else 0)
          else 0) =
        (∑ σ : Fin n → Fin m, if σ j = i then μ σ * p i j else 0) +
          ∑ σ : Fin n → Fin m,
            ∑ k ∈ univ.filter (fun k => prec p w i k j),
              if σ j = i ∧ σ k = i then μ σ * p i k else 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    by_cases hσj : σ j = i
    · simp only [hσj, ↓reduceIte, true_and, mul_add, Finset.mul_sum, mul_ite, mul_zero]
    · simp only [hσj, ↓reduceIte, false_and, Finset.sum_const_zero, add_zero]
  rw [h2]
  congr 1
  · rw [← Finset.sum_filter, Finset.sum_mul]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_filter, Finset.sum_mul]
