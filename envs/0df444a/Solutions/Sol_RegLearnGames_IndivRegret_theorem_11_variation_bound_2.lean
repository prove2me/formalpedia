-- Prove2me | solution 2 for RegLearnGames.IndivRegret.theorem_11_variation_bound
-- status  : ACCEPTED   (prove)
-- author  : @suzukasan
-- created : 2026-10-21T10:22:17.046628+00:00
-- url     : https://prove2.me/submissions/6ebb2506-4bf4-474f-aad4-19b2fe3cea0e

import Mathlib
import Definitions.Def_RegLearnGames_TotalRegret_Setting
import Theorems.Thm_RegLearnGames_TotalRegret_display_2

open Finset RegLearnGames.TotalRegret

theorem solution {n d : ℕ} (u : Fin n → (Fin n → Fin d) → ℝ)
    (hu : ∀ i s, u i s ∈ Set.Icc (0 : ℝ) 1)
    (w w' : Fin n → Fin d → ℝ)
    (hw : ∀ j, w j ∈ stdSimplex ℝ (Fin d)) (hw' : ∀ j, w' j ∈ stdSimplex ℝ (Fin d))
    (κ : ℝ) (hκ : ∀ j, RegLearnGames.TotalRegret.l1 (w j - w' j) ≤ κ) :
    ∀ i, ‖RegLearnGames.TotalRegret.utilVec u w i - RegLearnGames.TotalRegret.utilVec u w' i‖ ^ 2 ≤
        ((n : ℝ) - 1) * ∑ j ∈ Finset.univ.erase i, RegLearnGames.TotalRegret.l1 (w j - w' j) ^ 2 ∧
      ((n : ℝ) - 1) * ∑ j ∈ Finset.univ.erase i, RegLearnGames.TotalRegret.l1 (w j - w' j) ^ 2 ≤
        ((n : ℝ) - 1) ^ 2 * κ ^ 2 := by
  classical
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
  have hfirst : ‖utilVec u w i - utilVec u w' i‖ ^ 2 ≤
      ((n : ℝ) - 1) * ∑ j ∈ univ.erase i, l1 (w j - w' j) ^ 2 := by
    nlinarith [norm_nonneg (utilVec u w i - utilVec u w' i)]
  refine ⟨hfirst, ?_⟩
  have hsum : (∑ j ∈ univ.erase i, l1 (w j - w' j) ^ 2) ≤
      ((univ.erase i).card : ℝ) * κ ^ 2 := by
    calc
      _ ≤ ∑ j ∈ univ.erase i, κ ^ 2 := by
        refine sum_le_sum fun j _ => ?_
        have h0 : 0 ≤ l1 (w j - w' j) := sum_nonneg fun _ _ => abs_nonneg _
        have h := hκ j
        nlinarith
      _ = _ := by simp
  rw [hcard] at hsum
  have hn0 : (0 : ℝ) ≤ (n : ℝ) - 1 := by
    have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hmul := mul_le_mul_of_nonneg_left hsum hn0
  nlinarith
