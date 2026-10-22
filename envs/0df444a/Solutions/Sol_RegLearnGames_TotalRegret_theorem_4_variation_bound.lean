-- Prove2me | solution 1 for RegLearnGames.TotalRegret.theorem_4_variation_bound
-- status  : ACCEPTED   (prove)
-- author  : @suzukasan
-- created : 2026-10-21T10:17:51.89511+00:00
-- url     : https://prove2.me/submissions/579d3fab-0b25-4dc4-8caf-2c293d3caa27

import Mathlib
import Definitions.Def_RegLearnGames_TotalRegret_Setting
import Theorems.Thm_RegLearnGames_TotalRegret_display_2

open Finset RegLearnGames.TotalRegret

theorem solution {n d : ℕ} (u : Fin n → (Fin n → Fin d) → ℝ)
    (hu : ∀ i s, u i s ∈ Set.Icc (0 : ℝ) 1)
    (w w' : Fin n → Fin d → ℝ) (hw : ∀ j, w j ∈ stdSimplex ℝ (Fin d))
    (hw' : ∀ j, w' j ∈ stdSimplex ℝ (Fin d)) :
    ∑ i, ‖utilVec u w i - utilVec u w' i‖ ^ 2 ≤
      ((n : ℝ) - 1) * ∑ i, ∑ j ∈ Finset.univ.erase i, l1 (w j - w' j) ^ 2 ∧
    ((n : ℝ) - 1) * ∑ i, ∑ j ∈ Finset.univ.erase i, l1 (w j - w' j) ^ 2 =
      ((n : ℝ) - 1) ^ 2 * ∑ i, l1 (w i - w' i) ^ 2 := by
  classical
  have hpoint : ∀ i : Fin n,
      ‖utilVec u w i - utilVec u w' i‖ ^ 2 ≤
        ((n : ℝ) - 1) * ∑ j ∈ univ.erase i, l1 (w j - w' j) ^ 2 := by
    intro i
    have hn : 1 ≤ n := by have := i.isLt; omega
    have hcard : ((univ.erase i).card : ℝ) = (n : ℝ) - 1 := by
      rw [card_erase_of_mem (mem_univ i), card_univ, Fintype.card_fin,
        Nat.cast_sub hn]
      simp
    have hs : (∑ j : {j : Fin n // j ≠ i}, l1 (w j.1 - w' j.1)) =
        ∑ j ∈ univ.erase i, l1 (w j - w' j) := by
      exact (sum_subtype (univ.erase i) (by intro j; simp)
        (fun j => l1 (w j - w' j))).symm
    have hd := display_2 u hu w w' hw hw' i
    have hnorm := hd.1.trans hd.2
    rw [hs] at hnorm
    have hcs := sq_sum_le_card_mul_sum_sq (s := univ.erase i)
      (f := fun j => l1 (w j - w' j))
    rw [hcard] at hcs
    have hnonneg : 0 ≤ ∑ j ∈ univ.erase i, l1 (w j - w' j) :=
      sum_nonneg fun j _ => sum_nonneg fun _ _ => abs_nonneg _
    nlinarith [norm_nonneg (utilVec u w i - utilVec u w' i)]
  have hdouble : (∑ i : Fin n, ∑ j ∈ univ.erase i, l1 (w j - w' j) ^ 2) =
      ((n : ℝ) - 1) * ∑ j, l1 (w j - w' j) ^ 2 := by
    calc
      _ = ∑ i : Fin n, ((∑ j, l1 (w j - w' j) ^ 2) - l1 (w i - w' i) ^ 2) := by
        refine sum_congr rfl fun i _ => ?_
        exact sum_erase_eq_sub (mem_univ i)
      _ = _ := by
        simp only [sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
  constructor
  · calc
      _ ≤ ∑ i : Fin n, ((n : ℝ) - 1) * ∑ j ∈ univ.erase i, l1 (w j - w' j) ^ 2 :=
        sum_le_sum fun i _ => hpoint i
      _ = _ := by rw [mul_sum]
  · rw [hdouble]
    ring
