-- Prove2me | solution 1 for SupplyChainTheory.variable_fixing
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-25T22:45:18.561698+00:00
-- url     : https://prove2.me/submissions/d72fa79c-ccfb-4513-b3fb-4b6898f78930

import Mathlib
import Definitions.Def_SupplyChainTheory_location
import Theorems.Thm_SupplyChainTheory_lagrangian_subproblem

open SupplyChainTheory


/-- Site-by-site lower bound: `lagrObjective ≥ ∑ⱼ (βⱼ + fⱼ) xⱼ + ∑ᵢ λᵢ` for `0 ≤ y ≤ x`. -/
private lemma lagr_lower_sites {n m : ℕ} (h : Fin n → ℝ) (c : Fin n → Fin m → ℝ) (f : Fin m → ℝ)
    (lam : Fin n → ℝ) (x : Fin m → ℝ) (y : Fin n → Fin m → ℝ)
    (hyx : ∀ i j, y i j ≤ x j) (hy : ∀ i j, 0 ≤ y i j) :
    ∑ j, (benefit h c lam j + f j) * x j + ∑ i, lam i ≤ lagrObjective h c f lam x y := by
  rw [lagrObjective, Finset.sum_comm (f := fun i j => (h i * c i j - lam i) * y i j)]
  have hj : ∀ j, (benefit h c lam j + f j) * x j ≤ f j * x j + ∑ i, (h i * c i j - lam i) * y i j := by
    intro j
    have hterm : ∀ i, min 0 (h i * c i j - lam i) * x j ≤ (h i * c i j - lam i) * y i j := by
      intro i
      rcases le_total 0 (h i * c i j - lam i) with hpos | hneg
      · rw [min_eq_left hpos, zero_mul]; exact mul_nonneg hpos (hy i j)
      · rw [min_eq_right hneg]; exact mul_le_mul_of_nonpos_left (hyx i j) hneg
    have hsum : benefit h c lam j * x j ≤ ∑ i, (h i * c i j - lam i) * y i j := by
      rw [benefit, Finset.sum_mul]; exact Finset.sum_le_sum (fun i _ => hterm i)
    linarith
  have := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hj j)
  rw [Finset.sum_add_distrib] at this
  linarith

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
    (_hm : 0 < m) (lam : Fin n → ℝ) (UB : ℝ) (hUB : uflpOpt h c f ≤ UB) (j : Fin m) :
    (0 ≤ benefit h c lam j + f j → UB < zLR h c f lam + (benefit h c lam j + f j) →
        ∀ x y, UFLPFeasible x y → uflpCost h c f x y = uflpOpt h c f → x j = 0)
      ∧ (benefit h c lam j + f j < 0 → UB < zLR h c f lam - (benefit h c lam j + f j) →
        ∀ x y, UFLPFeasible x y → uflpCost h c f x y = uflpOpt h c f → x j = 1) := by
  -- Theorem 8.1: `z_LR(λ) = ∑ⱼ min{0, βⱼ + fⱼ} + ∑ᵢ λᵢ`.
  have hz := (lagrangian_subproblem h c f lam).2.2
  set g : Fin m → ℝ := fun k => benefit h c lam k + f k with hg
  -- For a feasible `x`, compare `∑ gₖ xₖ` with `∑ min{0, gₖ}` away from `j`.
  have hcmp : ∀ x : Fin m → ℝ, (∀ k, x k = 0 ∨ x k = 1) →
      ∑ k, min 0 (g k) + (g j * x j - min 0 (g j)) ≤ ∑ k, g k * x k := by
    intro x hx
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), ← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    have : ∑ k ∈ Finset.univ.erase j, min 0 (g k) ≤ ∑ k ∈ Finset.univ.erase j, g k * x k :=
      Finset.sum_le_sum (fun k _ => by
        rcases hx k with h0 | h1
        · rw [h0, mul_zero]; exact min_le_left _ _
        · rw [h1, mul_one]; exact min_le_right _ _)
    linarith
  have hcost : ∀ x y, UFLPFeasible x y →
      ∑ k, g k * x k + ∑ i, lam i ≤ uflpCost h c f x y := by
    rintro x y ⟨hsum, hyx, -, hy⟩
    rw [← lagr_eq_cost h c f lam x y hsum]
    exact lagr_lower_sites h c f lam x y hyx hy
  refine ⟨fun hpos hgap x y hxy hopt => ?_, fun hneg hgap x y hxy hopt => ?_⟩
  · -- If `j` were open, the cost would exceed `z_LR(λ) + βⱼ + fⱼ > UB`.
    rcases hxy.2.2.1 j with h0 | h1
    · exact h0
    exfalso
    have := hcmp x hxy.2.2.1
    rw [h1, mul_one, min_eq_left hpos] at this
    have := hcost x y hxy
    rw [hz] at hgap
    simp only [hg] at *
    linarith
  · -- If `j` were closed, the cost would exceed `z_LR(λ) − (βⱼ + fⱼ) > UB`.
    rcases hxy.2.2.1 j with h0 | h1
    · exfalso
      have := hcmp x hxy.2.2.1
      rw [h0, mul_zero, min_eq_right hneg.le] at this
      have := hcost x y hxy
      rw [hz] at hgap
      simp only [hg] at *
      linarith
    · exact h1
