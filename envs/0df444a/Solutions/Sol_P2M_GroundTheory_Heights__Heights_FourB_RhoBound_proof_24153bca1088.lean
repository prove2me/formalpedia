-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FourB_RhoBound_proof_24153bca1088
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:55:00.287073+00:00
-- url     : https://prove2.me/submissions/2434362a-fd1c-4901-aec3-b718443f7e2d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_PRhoBound
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_card_window_fin_23e7026002b7
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB
open Finset
namespace GroundTheory.Heights₂.Heights.FourB
namespace RhoBound
theorem _root_.solution (h : DegreeRatio.Statement) : RhoBound.Statement := by
  intro f k j j' x g₁ T w hH
  obtain ⟨hk, hg, hT, hw, hdec, hacr, hcloud⟩ := hH
  intro N ρ
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hg0 : 0 < g₁ := lt_of_le_of_lt (by positivity) hg
  have hδ : DegreeRatio.Hyp (k + j + j' - 1) j' x (3 * N) :=
    ⟨by positivity, hdec, fun τ i l hil => lt_of_lt_of_le hg (hacr τ i l hil)⟩
  obtain ⟨-, -, hle1, hsum⟩ := h f (k + j + j' - 1) j' x (3 * N) hδ

  have key : ∀ τ, ∑ i : Fin (k + j + j' - 1), ∑ l : Fin (k + j + j' - 1),
      (if Across (k + j + j' - 1) j' i l then 3 * N / (x τ i - x τ l) else 0) ≤
      3 * N * ((j : ℝ) * j' / g₁ + 2 * ((k : ℝ) - 1) * j' * T / w τ) := by
    intro τ
    set A : Fin (k + j + j' - 1) → ℝ := fun i => if 0 ≤ i.val ∧ i.val < k - 1 then 1 else 0
    set C : Fin (k + j + j' - 1) → ℝ := fun i => if k - 1 ≤ i.val ∧ i.val < k + j - 1 then 1 else 0
    set B : Fin (k + j + j' - 1) → ℝ :=
      fun l => if k + j - 1 ≤ l.val ∧ l.val < k + j + j' - 1 then 1 else 0
    have hterm : ∀ i l : Fin (k + j + j' - 1),
        (if Across (k + j + j' - 1) j' i l then 3 * N / (x τ i - x τ l) else 0) ≤
          3 * N * (2 * T / w τ) * (A i * B l) + 3 * N * (1 / g₁) * (C i * B l) := by
      intro i l
      have hT' : 0 ≤ 3 * N * (2 * T / w τ) := by have := hw τ; positivity
      have hg' : 0 ≤ 3 * N * (1 / g₁) := by positivity
      have hA0 : 0 ≤ A i := by simp only [A]; split_ifs <;> norm_num
      have hB0 : 0 ≤ B l := by simp only [B]; split_ifs <;> norm_num
      have hC0 : 0 ≤ C i := by simp only [C]; split_ifs <;> norm_num
      by_cases hA : Across (k + j + j' - 1) j' i l
      · rw [if_pos hA]
        have hd : g₁ ≤ x τ i - x τ l := hacr τ i l hA
        have hdpos : 0 < x τ i - x τ l := lt_of_lt_of_le hg0 hd
        have hB1 : B l = 1 := by
          simp only [B]; rw [if_pos]; unfold Across at hA; have := l.isLt; omega
        by_cases hc : i.val < k - 1
        · have hA1 : A i = 1 := by simp only [A]; rw [if_pos]; omega
          have hC1 : C i = 0 := by simp only [C]; rw [if_neg]; omega
          rw [hA1, hB1, hC1]
          have hwd : w τ / (2 * T) ≤ x τ i - x τ l := hcloud τ i l hc hA
          have hwpos : 0 < w τ / (2 * T) := by have := hw τ; positivity
          have : 1 / (x τ i - x τ l) ≤ 2 * T / w τ := by
            rw [div_le_div_iff₀ hdpos (hw τ)]
            rw [div_le_iff₀ (by positivity)] at hwd
            linarith
          calc 3 * N / (x τ i - x τ l) = 3 * N * (1 / (x τ i - x τ l)) := by ring
            _ ≤ 3 * N * (2 * T / w τ) := mul_le_mul_of_nonneg_left this (by positivity)
            _ = _ := by ring
        · have hA1 : A i = 0 := by simp only [A]; rw [if_neg]; omega
          have hC1 : C i = 1 := by
            simp only [C]; rw [if_pos]; unfold Across at hA; omega
          rw [hA1, hB1, hC1]
          have : 1 / (x τ i - x τ l) ≤ 1 / g₁ := one_div_le_one_div_of_le hg0 hd
          calc 3 * N / (x τ i - x τ l) = 3 * N * (1 / (x τ i - x τ l)) := by ring
            _ ≤ 3 * N * (1 / g₁) := mul_le_mul_of_nonneg_left this (by positivity)
            _ = _ := by ring
      · rw [if_neg hA]; positivity
    have hAs : ∑ i, A i = ((k - 1 - 0 : ℕ) : ℝ) := card_window_fin _ 0 (k - 1) (by omega)
    have hCs : ∑ i, C i = ((k + j - 1 - (k - 1) : ℕ) : ℝ) := card_window_fin _ _ _ (by omega)
    have hBs : ∑ l, B l = ((k + j + j' - 1 - (k + j - 1) : ℕ) : ℝ) :=
      card_window_fin _ _ _ le_rfl
    have e1 : k - 1 - 0 = k - 1 := by omega
    have e2 : k + j - 1 - (k - 1) = j := by omega
    have e3 : k + j + j' - 1 - (k + j - 1) = j' := by omega
    rw [e1] at hAs; rw [e2] at hCs; rw [e3] at hBs
    calc _ ≤ ∑ i : Fin (k + j + j' - 1), ∑ l : Fin (k + j + j' - 1),
          (3 * N * (2 * T / w τ) * (A i * B l) + 3 * N * (1 / g₁) * (C i * B l)) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun l _ => hterm i l
      _ = 3 * N * (2 * T / w τ) * ((∑ i, A i) * ∑ l, B l) +
            3 * N * (1 / g₁) * ((∑ i, C i) * ∑ l, B l) := by
          simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_mul_sum]
      _ = _ := by
          rw [hAs, hBs, hCs, Nat.cast_sub hk]
          have := hw τ
          field_simp
          ring
  refine ⟨by simp only [ρ]; linarith, ?_, ?_⟩
  · calc ρ ≤ ∑ τ, ∑ i : Fin (k + j + j' - 1), ∑ l : Fin (k + j + j' - 1),
          (if Across (k + j + j' - 1) j' i l then 3 * N / (x τ i - x τ l) else 0) := hsum
      _ ≤ ∑ τ, 3 * N * ((j : ℝ) * j' / g₁ + 2 * ((k : ℝ) - 1) * j' * T / w τ) :=
          Finset.sum_le_sum fun τ _ => key τ
      _ = _ := by rw [Finset.mul_sum]
  · rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun τ _ => ?_
    have hwτ := hw τ
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg _
    have hj' : (0 : ℝ) ≤ j' := Nat.cast_nonneg _
    have h1 : (j : ℝ) * j' / g₁ ≤ 2 * (((j : ℝ) + j') ^ 2 / g₁) := by
      rw [← mul_div_assoc, div_le_div_iff_of_pos_right hg0]; nlinarith
    have h2 : 2 * ((k : ℝ) - 1) * j' * T / w τ ≤ 2 * (((j : ℝ) + j') * k * T / w τ) := by
      rw [← mul_div_assoc, div_le_div_iff_of_pos_right hwτ]
      have : ((k : ℝ) - 1) * j' ≤ ((j : ℝ) + j') * k := by nlinarith
      nlinarith
    nlinarith
end RhoBound
end GroundTheory.Heights₂.Heights.FourB
