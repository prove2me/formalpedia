-- Prove2me | solution 1 for ProcureAssort.Hotelling.lemma_F_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T03:14:37.458122+00:00
-- url     : https://prove2.me/submissions/c19f5df7-2b5a-4503-9546-687143f5f20e

import Mathlib
import Definitions.Def_ProcureAssort_Hotelling_Setting

open ProcureAssort.Hotelling

theorem PA_pathA_rowsum {n : ℕ} (Q : Finset (Fin n)) (i : Fin n) (hi : i ∈ Q) :
    ∑ j ∈ Q, pathA Q i j = 0 := by
  classical
  have h1 : ∀ j ∈ Q, pathA Q i j =
      (if i = j then -(((Q.filter (fun k => Adjacent Q i k)).card : ℕ) : ℝ) else 0) +
        (if Adjacent Q i j then 1 else 0) := by
    intro j hj
    unfold pathA
    rw [if_pos ⟨hi, hj⟩]
    by_cases hij : i = j
    · subst hij
      have : ¬ Adjacent Q i i := fun h => h.2.2.1 rfl
      simp [this]
    · simp [hij]
  rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_ite_eq Q i, if_pos hi,
    ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  ring

theorem solution
    (n : ℕ) (hn : 2 ≤ n)
    (Θ : Fin n → Finset ℝ) (hΘ : ∀ i, ∀ c ∈ Θ i, 0 < c)
    (f : Fin n → ℝ → ℝ) (hf0 : ∀ i, ∀ c ∈ Θ i, 0 < f i c) (hf1 : ∀ i, ∑ c ∈ Θ i, f i c = 1)
    (hreg : ∀ i, StrictMonoOn (virtualCost Θ f i) ((Θ i : Finset ℝ) : Set ℝ))
    (ℓ : Fin n → ℝ) (hℓ : StrictMono ℓ) (hℓ0 : ∀ i, 0 ≤ ℓ i) (hℓ1 : ∀ i, ℓ i ≤ 1)
    (δ : ℝ) (hδ : 0 < δ)
    (a : Profile Θ → Fin n → ℝ) (b : Fin n → ℝ → ℝ)
    (h14 : ∀ θ : Profile Θ, ∀ j ∈ activeSet Θ f ℓ δ θ,
      (∑ i ∈ activeSet Θ f ℓ δ θ, a θ i * pathA (activeSet Θ f ℓ δ θ) i j)
        + b j (θ j) * probOthers f j θ * xstar Θ f ℓ δ θ j = 0) :
    ∀ θ : Profile Θ,
      ∑ i ∈ activeSet Θ f ℓ δ θ, b i (θ i) / f i (θ i) * xstar Θ f ℓ δ θ i = 0 := by
  intro θ
  set Q := activeSet Θ f ℓ δ θ
  have hsum := Finset.sum_eq_zero (s := Q) (fun j hj => h14 θ j hj)
  rw [Finset.sum_add_distrib, Finset.sum_comm] at hsum
  have hz : ∑ i ∈ Q, ∑ j ∈ Q, a θ i * pathA Q i j = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [← Finset.mul_sum, PA_pathA_rowsum Q i hi, mul_zero]
  rw [hz, zero_add] at hsum
  have hfpos : ∀ j, 0 < f j (θ j) := fun j => hf0 j _ (θ j).2
  have hprob : ∀ j, prob f θ = f j (θ j) * probOthers f j θ := by
    intro j
    unfold prob probOthers
    rw [Finset.mul_prod_erase _ (fun k => f k (θ k)) (Finset.mem_univ j)]
  have hppos : 0 < prob f θ := Finset.prod_pos fun j _ => hfpos j
  have : prob f θ * ∑ i ∈ Q, b i (θ i) / f i (θ i) * xstar Θ f ℓ δ θ i = 0 := by
    rw [Finset.mul_sum, ← hsum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hprob j]
    have := (hfpos j).ne'
    field_simp
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h hppos.ne'
  · exact h
