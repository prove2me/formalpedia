-- Prove2me | solution 1 for SupplyChainTheory.lagrangian_subproblem
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-25T22:42:29.039154+00:00
-- url     : https://prove2.me/submissions/3af6371c-6e3c-4889-ba5f-aa77cdcc84c6

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

theorem solution {n m : ℕ} (h : Fin n → ℝ) (c : Fin n → Fin m → ℝ) (f : Fin m → ℝ)
    (lam : Fin n → ℝ) :
    LagrFeasible (lagrX h c f lam) (lagrY h c f lam)
      ∧ lagrObjective h c f lam (lagrX h c f lam) (lagrY h c f lam)
          = ∑ j, min 0 (benefit h c lam j + f j) + ∑ i, lam i
      ∧ zLR h c f lam = ∑ j, min 0 (benefit h c lam j + f j) + ∑ i, lam i := by
  have hX01 : ∀ j, lagrX h c f lam j = 0 ∨ lagrX h c f lam j = 1 := by
    intro j; unfold lagrX; split_ifs <;> simp
  have hfeas : LagrFeasible (lagrX h c f lam) (lagrY h c f lam) := by
    refine ⟨fun i j => ?_, hX01, fun i j => ?_⟩
    · unfold lagrY; split_ifs with hh
      · rw [hh.1]
      · exact (binary_mem (hX01 j)).1
    · unfold lagrY; split_ifs <;> norm_num
  -- Evaluate the objective site by site.
  have hval : lagrObjective h c f lam (lagrX h c f lam) (lagrY h c f lam)
      = ∑ j, min 0 (benefit h c lam j + f j) + ∑ i, lam i := by
    rw [lagrObjective, Finset.sum_comm (f := fun i j => (h i * c i j - lam i) * lagrY h c f lam i j),
      ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    by_cases hj : benefit h c lam j + f j < 0
    · have hX : lagrX h c f lam j = 1 := by unfold lagrX; rw [if_pos hj]
      rw [min_eq_right hj.le, hX, mul_one, benefit, add_comm (∑ i, _) (f j)]
      congr 1
      refine Finset.sum_congr rfl (fun i _ => ?_)
      unfold lagrY; rw [hX]
      by_cases hi : h i * c i j - lam i < 0
      · rw [if_pos ⟨rfl, hi⟩, mul_one, min_eq_right hi.le]
      · rw [if_neg (fun h' => hi h'.2), mul_zero, min_eq_left (not_lt.mp hi)]
    · have hX : lagrX h c f lam j = 0 := by unfold lagrX; rw [if_neg hj]
      rw [min_eq_left (not_lt.mp hj), hX, mul_zero, zero_add]
      refine Finset.sum_eq_zero (fun i _ => ?_)
      unfold lagrY; rw [hX, if_neg (fun h' => by norm_num at h'), mul_zero]
  refine ⟨hfeas, hval, ?_⟩
  -- The value is attained and is a lower bound, hence the infimum.
  refine IsLeast.csInf_eq ⟨⟨_, _, hfeas, hval.symm⟩, ?_⟩
  rintro z ⟨x, y, ⟨hyx, hx, hy⟩, rfl⟩
  exact lagr_lower h c f lam x y (fun j => binary_mem (hx j)) hyx hy
