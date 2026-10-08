-- Prove2me | solution 1 for VidalHGS.Elitism.elite_biasedFitness_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-07T22:33:03.423777+00:00
-- url     : https://prove2.me/submissions/16076ea0-9f5a-46f7-939e-30051f5c28ee

import Mathlib
import Definitions.Def_VidalHGS_Elitism_SurvivorSelection

open VidalHGS.Elitism

theorem solution {α : Type*} [DecidableEq α]
    (c : α → ℝ) (Δ : Finset α → α → ℝ) (nbElit : ℕ) (P : Finset α) (J : α)
    (hsize : nbElit + 1 ≤ P.card) (hJ : J ∈ P) (helite : IsElite c nbElit P J) :
    biasedFitness c Δ nbElit P J ≤
        ((nbElit : ℝ) - 1) / ((P.card : ℝ) - 1) + 1 - (nbElit : ℝ) / ((P.card : ℝ) - 1) ∧
      biasedFitness c Δ nbElit P J < 1 := by
  have hElit1 : 1 ≤ nbElit := by
    unfold IsElite at helite
    omega
  have hcard2 : 2 ≤ P.card := by omega
  have hden : (0 : ℝ) < (P.card : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (P.card : ℝ) := by exact_mod_cast hcard2
    linarith
  have hdiv_le_one : ∀ x : ℝ, x ≤ (P.card : ℝ) - 1 → x / ((P.card : ℝ) - 1) ≤ 1 := by
    intro x hx
    have := div_le_div_of_nonneg_right hx hden.le
    rwa [div_self hden.ne'] at this
  -- the coefficient of the diversity rank is nonnegative since nbElit ≤ |P| - 1
  have hcoef : (0 : ℝ) ≤ 1 - (nbElit : ℝ) / ((P.card : ℝ) - 1) := by
    have h1 : (nbElit : ℝ) ≤ (P.card : ℝ) - 1 := by
      have : (nbElit : ℝ) + 1 ≤ (P.card : ℝ) := by exact_mod_cast hsize
      linarith
    have := hdiv_le_one _ h1
    linarith
  -- fitness rank bound: fewer than nbElit individuals are strictly better than J
  have hfit : fitRank c P J ≤ ((nbElit : ℝ) - 1) / ((P.card : ℝ) - 1) := by
    unfold fitRank
    have hnum : ((P.filter (fun K => c K < c J)).card : ℝ) ≤ (nbElit : ℝ) - 1 := by
      unfold IsElite at helite
      have : ((P.filter (fun K => c K < c J)).card : ℝ) + 1 ≤ (nbElit : ℝ) := by
        exact_mod_cast helite
      linarith
    exact div_le_div_of_nonneg_right hnum hden.le
  -- diversity rank bounds: 0 ≤ dc(J) ≤ 1
  have hdc0 : 0 ≤ dcRank Δ P J := by
    unfold dcRank
    exact div_nonneg (Nat.cast_nonneg _) hden.le
  have hdc1 : dcRank Δ P J ≤ 1 := by
    unfold dcRank
    apply hdiv_le_one
    have hsub : P.filter (fun K => Δ P J < Δ P K) ⊆ P.erase J := by
      intro K hK
      rw [Finset.mem_filter] at hK
      rw [Finset.mem_erase]
      refine ⟨?_, hK.1⟩
      intro hKJ
      rw [hKJ] at hK
      exact lt_irrefl _ hK.2
    have hle := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hJ] at hle
    have h' : ((P.filter (fun K => Δ P J < Δ P K)).card : ℝ) ≤ ((P.card - 1 : ℕ) : ℝ) := by
      exact_mod_cast hle
    rwa [Nat.cast_pred (by omega)] at h'
  have hBF : biasedFitness c Δ nbElit P J =
      fitRank c P J + (1 - (nbElit : ℝ) / ((P.card : ℝ) - 1)) * dcRank Δ P J := rfl
  have hmain : biasedFitness c Δ nbElit P J ≤
      ((nbElit : ℝ) - 1) / ((P.card : ℝ) - 1) + 1 - (nbElit : ℝ) / ((P.card : ℝ) - 1) := by
    rw [hBF]
    have := mul_le_mul_of_nonneg_left hdc1 hcoef
    linarith
  refine ⟨hmain, ?_⟩
  have hlt : ((nbElit : ℝ) - 1) / ((P.card : ℝ) - 1) + 1 - (nbElit : ℝ) / ((P.card : ℝ) - 1) < 1 := by
    have hsplit : ((nbElit : ℝ) - 1) / ((P.card : ℝ) - 1) =
        (nbElit : ℝ) / ((P.card : ℝ) - 1) - 1 / ((P.card : ℝ) - 1) := by
      rw [sub_div]
    have hpos : 0 < 1 / ((P.card : ℝ) - 1) := one_div_pos.mpr hden
    linarith
  exact lt_of_le_of_lt hmain hlt
