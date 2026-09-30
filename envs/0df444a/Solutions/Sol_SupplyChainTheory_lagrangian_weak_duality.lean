-- Prove2me | solution 1 for SupplyChainTheory.lagrangian_weak_duality
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-25T22:42:29.938371+00:00
-- url     : https://prove2.me/submissions/14cc2d57-da16-442f-a83c-d15581f37435

import Mathlib
import Definitions.Def_SupplyChainTheory_location

open SupplyChainTheory

/-- **Lower bound for the Lagrangian objective.** For `0 ≤ xⱼ ≤ 1` and `0 ≤ yᵢⱼ ≤ xⱼ`, the
Lagrangian objective is at least `∑ⱼ min{0, βⱼ + fⱼ} + ∑ᵢ λᵢ`. -/
private lemma lagr_lower {n m : ℕ} (h : Fin n → ℝ) (c : Fin n → Fin m → ℝ) (f : Fin m → ℝ)
    (lam : Fin n → ℝ) (x : Fin m → ℝ) (y : Fin n → Fin m → ℝ)
    (hx : ∀ j, 0 ≤ x j ∧ x j ≤ 1) (hyx : ∀ i j, y i j ≤ x j) (hy : ∀ i j, 0 ≤ y i j) :
    ∑ j, min 0 (benefit h c lam j + f j) + ∑ i, lam i ≤ lagrObjective h c f lam x y := by
  rw [lagrObjective, Finset.sum_comm (f := fun i j => (h i * c i j - lam i) * y i j)]
  have hj : ∀ j, min 0 (benefit h c lam j + f j)
      ≤ f j * x j + ∑ i, (h i * c i j - lam i) * y i j := by
    intro j
    -- Each term is at least `min{0, hᵢcᵢⱼ − λᵢ} · xⱼ`.
    have hterm : ∀ i, min 0 (h i * c i j - lam i) * x j ≤ (h i * c i j - lam i) * y i j := by
      intro i
      rcases le_total 0 (h i * c i j - lam i) with hpos | hneg
      · rw [min_eq_left hpos, zero_mul]; exact mul_nonneg hpos (hy i j)
      · rw [min_eq_right hneg]; exact mul_le_mul_of_nonpos_left (hyx i j) hneg
    have hsum : benefit h c lam j * x j ≤ ∑ i, (h i * c i j - lam i) * y i j := by
      rw [benefit, Finset.sum_mul]; exact Finset.sum_le_sum (fun i _ => hterm i)
    rcases le_total 0 (benefit h c lam j + f j) with hpos | hneg
    · rw [min_eq_left hpos]; nlinarith [(hx j).1]
    · rw [min_eq_right hneg]; nlinarith [(hx j).2]
  have := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hj j)
  rw [Finset.sum_add_distrib] at this
  linarith

private lemma binary_mem {x : ℝ} (hx : x = 0 ∨ x = 1) : 0 ≤ x ∧ x ≤ 1 := by
  rcases hx with rfl | rfl <;> norm_num

/-- A feasible UFLP solution: open everything, assign every customer to site `j₀`. -/
private lemma uflp_nonempty {n m : ℕ} (h : Fin n → ℝ) (c : Fin n → Fin m → ℝ) (f : Fin m → ℝ)
    (hm : 0 < m) : {z | ∃ x y, UFLPFeasible x y ∧ z = uflpCost h c f x y}.Nonempty := by
  classical
  refine ⟨_, fun _ => 1, fun _ j => if j = ⟨0, hm⟩ then 1 else 0, ⟨fun i => ?_, fun i j => ?_,
    fun j => Or.inr rfl, fun i j => ?_⟩, rfl⟩
  · simp
  · simp only []; split_ifs <;> norm_num
  · simp only []; split_ifs <;> norm_num

/-- On UFLP-feasible solutions the Lagrangian objective equals the UFLP cost. -/
private lemma lagr_eq_cost {n m : ℕ} (h : Fin n → ℝ) (c : Fin n → Fin m → ℝ) (f : Fin m → ℝ)
    (lam : Fin n → ℝ) (x : Fin m → ℝ) (y : Fin n → Fin m → ℝ) (hsum : ∀ i, ∑ j, y i j = 1) :
    lagrObjective h c f lam x y = uflpCost h c f x y := by
  rw [lagrObjective, uflpCost]
  have : ∀ i, ∑ j, (h i * c i j - lam i) * y i j = ∑ j, h i * c i j * y i j - lam i := by
    intro i
    simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hsum i, mul_one]
  simp only [this, Finset.sum_sub_distrib]
  ring

theorem solution {n m : ℕ} (h : Fin n → ℝ) (c : Fin n → Fin m → ℝ) (f : Fin m → ℝ)
    (hm : 0 < m) (lam : Fin n → ℝ) : zLR h c f lam ≤ uflpOpt h c f := by
  have hbdd : BddBelow {z | ∃ x y, LagrFeasible x y ∧ z = lagrObjective h c f lam x y} := by
    refine ⟨∑ j, min 0 (benefit h c lam j + f j) + ∑ i, lam i, ?_⟩
    rintro z ⟨x, y, ⟨hyx, hx, hy⟩, rfl⟩
    exact lagr_lower h c f lam x y (fun j => binary_mem (hx j)) hyx hy
  refine le_csInf (uflp_nonempty h c f hm) ?_
  rintro z ⟨x, y, ⟨hsum, hyx, hx, hy⟩, rfl⟩
  rw [← lagr_eq_cost h c f lam x y hsum]
  exact csInf_le hbdd ⟨x, y, ⟨hyx, hx, hy⟩, rfl⟩
