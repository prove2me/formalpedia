-- Prove2me | solution 1 for SupplyChainTheory.lagrangian_equals_lp
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-25T22:59:09.423121+00:00
-- url     : https://prove2.me/submissions/70da58f4-626b-457c-8918-efbf5263b9b4

import Mathlib
import Definitions.Def_SupplyChainTheory_location
import Theorems.Thm_SupplyChainTheory_lagrangian_subproblem
import Theorems.Thm_SupplyChainTheory_lagrangian_dual_bounds

open SupplyChainTheory

/-- On any `y`, the Lagrangian objective is the UFLP cost minus the priced assignment violations. -/
private lemma lagr_eq_cost_sub {n m : ℕ} (h : Fin n → ℝ) (c : Fin n → Fin m → ℝ) (f : Fin m → ℝ)
    (lam : Fin n → ℝ) (x : Fin m → ℝ) (y : Fin n → Fin m → ℝ) :
    lagrObjective h c f lam x y = uflpCost h c f x y - ∑ i, lam i * (∑ j, y i j - 1) := by
  rw [lagrObjective, uflpCost]
  have : ∀ i, ∑ j, (h i * c i j - lam i) * y i j = ∑ j, h i * c i j * y i j - lam i * ∑ j, y i j := by
    intro i; rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  simp only [this, Finset.sum_sub_distrib, mul_sub, mul_one]
  ring

/-- **Lower bound for the Lagrangian objective** on `0 ≤ x ≤ 1`, `0 ≤ y ≤ x`. -/
private lemma lagr_lower {n m : ℕ} (h : Fin n → ℝ) (c : Fin n → Fin m → ℝ) (f : Fin m → ℝ)
    (lam : Fin n → ℝ) (x : Fin m → ℝ) (y : Fin n → Fin m → ℝ)
    (hx : ∀ j, 0 ≤ x j ∧ x j ≤ 1) (hyx : ∀ i j, y i j ≤ x j) (hy : ∀ i j, 0 ≤ y i j) :
    ∑ j, min 0 (benefit h c lam j + f j) + ∑ i, lam i ≤ lagrObjective h c f lam x y := by
  rw [lagrObjective, Finset.sum_comm (f := fun i j => (h i * c i j - lam i) * y i j)]
  have hj : ∀ j, min 0 (benefit h c lam j + f j)
      ≤ f j * x j + ∑ i, (h i * c i j - lam i) * y i j := by
    intro j
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

/-- The UFLP cost is linear in `(x, y)`. -/
private lemma uflpCost_lin {n m : ℕ} (h : Fin n → ℝ) (c : Fin n → Fin m → ℝ) (f : Fin m → ℝ)
    (x x' : Fin m → ℝ) (y y' : Fin n → Fin m → ℝ) (a b : ℝ) :
    uflpCost h c f (a • x + b • x') (a • y + b • y')
      = a * uflpCost h c f x y + b * uflpCost h c f x' y' := by
  simp only [uflpCost, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib,
    Finset.mul_sum, mul_left_comm _ a, mul_left_comm _ b]
  ring

/-- The LP relaxation is feasible (open everything, assign to one site) and bounded below. -/
private lemma lp_nonempty {n m : ℕ} (hm : 0 < m) :
    ∃ (x : Fin m → ℝ) (y : Fin n → Fin m → ℝ), UFLPLPFeasible x y ∧ (∀ i, ∑ j, y i j = 1) := by
  classical
  refine ⟨fun _ => 1, fun _ j => if j = ⟨0, hm⟩ then 1 else 0, ⟨fun i => by simp, fun i j => ?_,
    fun j => by norm_num, fun i j => ?_⟩, fun i => by simp⟩
  · simp only []; split_ifs <;> norm_num
  · simp only []; split_ifs <;> norm_num

private lemma lp_bddBelow {n m : ℕ} (h : Fin n → ℝ) (c : Fin n → Fin m → ℝ) (f : Fin m → ℝ) :
    BddBelow {z | ∃ x y, UFLPLPFeasible x y ∧ z = uflpCost h c f x y} := by
  refine ⟨∑ j, min 0 (benefit h c 0 j + f j) + ∑ i, (0 : Fin n → ℝ) i, ?_⟩
  rintro z ⟨x, y, ⟨hsum, hyx, hx, hy⟩, rfl⟩
  have := lagr_lower h c f 0 x y hx hyx hy
  rw [lagr_eq_cost_sub] at this
  simpa using this


theorem solution {n m : ℕ} (h : Fin n → ℝ) (c : Fin n → Fin m → ℝ) (f : Fin m → ℝ)
    (hm : 0 < m) : uflpLP h c f = zLRbest h c f := by
  -- `z_LP ≤ z_LR` is the first half of (8.19).
  refine le_antisymm (lagrangian_dual_bounds h c f hm).1 ?_
  -- `z_LR(λ) ≤ z_LP` for every `λ`: the Lagrangian lower bound holds on the whole LP polytope.
  refine csSup_le (Set.range_nonempty _) ?_
  rintro _ ⟨lam, rfl⟩
  obtain ⟨-, -, hz⟩ := lagrangian_subproblem h c f lam
  obtain ⟨x₀, y₀, hf₀, -⟩ := lp_nonempty (n := n) hm
  refine le_csInf ⟨_, x₀, y₀, hf₀, rfl⟩ ?_
  rintro z ⟨x, y, ⟨hsum, hyx, hx, hy⟩, rfl⟩
  have hlow := lagr_lower h c f lam x y hx hyx hy
  rw [lagr_eq_cost_sub] at hlow
  simp only [hsum, sub_self, mul_zero, Finset.sum_const_zero, sub_zero] at hlow
  rw [hz]; exact hlow
