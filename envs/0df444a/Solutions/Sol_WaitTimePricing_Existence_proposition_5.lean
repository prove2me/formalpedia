-- Prove2me | solution 1 for WaitTimePricing.Existence.proposition_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T09:30:28.94469+00:00
-- url     : https://prove2.me/submissions/a03e456c-501f-4056-8be0-24a7974f8473

import Mathlib
import Definitions.Def_WaitTimePricing_Existence_Setting
import Definitions.Def_WaitTimePricing_Existence_Algorithm1
import Theorems.Thm_WaitTimePricing_Existence_lemma_2
import Theorems.Thm_WaitTimePricing_Existence_lemma_5

open Set Filter WaitTimePricing.Existence

theorem solution (M : Model) (hM : M.Standing) (obj : Objective) :
    (∀ j : ℕ, 1 ≤ j → 0 ≤ gN M obj (2 ^ j)) ∧
    (∀ j : ℕ, 1 ≤ j → gN M obj (2 ^ j) ≤ gN M obj (2 ^ (j + 1))) ∧
    (∀ j : ℕ, 1 ≤ j → gN M obj (2 ^ j) ≤ deriv M.U 0) ∧
    Tendsto (fun j : ℕ => gN M obj (2 ^ j)) atTop (nhds (gbar M obj)) := by
  have hw0 : 0 ≤ wbar M := Real.sSup_nonneg (fun x hx => le_of_lt hx.1)
  have h0mem : (0:ℝ) ∈ Icc 0 (wbar M + M.C) := ⟨le_rfl, by linarith [hM.C_pos]⟩
  have hU0 : 0 ≤ deriv M.U 0 := hM.deriv_U_nonneg 0 ⟨le_rfl, hM.C_pos.le⟩
  set S : ℕ → Set ℝ := fun N => {g : ℝ | 0 ≤ g ∧ KgN M obj g N 0 ≤ g} with hS
  have hbdd : ∀ N, BddBelow (S N) := fun N => ⟨0, fun x hx => hx.1⟩
  have hmem : ∀ N, 1 ≤ N → deriv M.U 0 ∈ S N := by
    intro N hN
    refine ⟨hU0, ?_⟩
    rw [lemma_5 M hM obj N hN 0 h0mem]; exact hU0
  have hsub : ∀ N, 1 ≤ N → S (2 * N) ⊆ S N := by
    intro N hN g hg
    exact ⟨hg.1, le_trans (lemma_2 M hM obj g hg.1 N hN 0 h0mem).2 hg.2⟩
  have hpow : ∀ j : ℕ, 1 ≤ 2 ^ j := fun j => Nat.one_le_two_pow
  have hnn : ∀ j : ℕ, 0 ≤ gN M obj (2 ^ j) := fun j => Real.sInf_nonneg (fun x hx => hx.1)
  have hmono : ∀ j : ℕ, gN M obj (2 ^ j) ≤ gN M obj (2 ^ (j + 1)) := by
    intro j
    have : 2 ^ (j + 1) = 2 * 2 ^ j := by ring
    show sInf (S (2 ^ j)) ≤ sInf (S (2 ^ (j + 1)))
    rw [this]
    exact csInf_le_csInf (hbdd _) ⟨_, hmem _ (by have := hpow j; omega)⟩ (hsub _ (hpow j))
  have hle : ∀ j : ℕ, gN M obj (2 ^ j) ≤ deriv M.U 0 := fun j => csInf_le (hbdd _) (hmem _ (hpow j))
  refine ⟨fun j _ => hnn j, fun j _ => hmono j, fun j _ => hle j, ?_⟩
  have hm : Monotone (fun j : ℕ => gN M obj (2 ^ j)) := monotone_nat_of_le_succ hmono
  have ht := tendsto_atTop_ciSup hm ⟨deriv M.U 0, by rintro _ ⟨j, rfl⟩; exact hle j⟩
  unfold gbar
  exact tendsto_nhds_limUnder ⟨_, ht⟩
