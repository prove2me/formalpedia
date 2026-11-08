-- Prove2me | solution 1 for RobustSPUA.theorem_7_routine_calculation
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:26:35.963584+00:00
-- url     : https://prove2.me/submissions/14566e1b-b35d-4d3f-8a3b-f97c1a4d5fa1

import Mathlib
import Definitions.Def_RobustSPUA_Model
import Definitions.Def_RobustSPUA_LP

open Finset

open RobustSPUA in
theorem solution (n : ℕ) (hn : 1 ≤ n) (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (x y : ℕ → ℕ → ℝ) (hxy : POL n p x y) :
    ∀ t ∈ Icc 2 n, slackLP p x t = polD p x y t := by
  intro t ht
  obtain ⟨h2, htn⟩ := Finset.mem_Icc.mp ht
  clear ht
  revert htn
  induction t, h2 using Nat.le_induction with
  | base =>
    intro _
    have e1 : Finset.Ico 1 2 = {1} := by
      ext k
      simp only [Finset.mem_Ico, Finset.mem_singleton]
      omega
    unfold slackLP polD
    rw [e1]
    simp only [Finset.sum_singleton, Finset.Icc_self, show (2:ℕ) - 1 = 1 from rfl]
    linarith [hxy.2.1]
  | succ t ht ih =>
    intro htn
    have htpos : (0:ℝ) < (t:ℝ) := by
      have : (2:ℝ) ≤ (t:ℝ) := by exact_mod_cast ht
      linarith
    have key : ∑ σ ∈ Icc 1 t, (y t σ + (1 - p) * x t σ) =
        polD p x y t - p * ∑ σ ∈ Icc 1 t, x t σ := by
      have h : ∀ σ ∈ Icc 1 t, y t σ + (1 - p) * x t σ =
          (1 / (t:ℝ)) * polD p x y t - p * x t σ := by
        intro σ hσ
        have := hxy.2.2 t (Finset.mem_Icc.mpr ⟨ht, by omega⟩) σ hσ
        linarith
      rw [Finset.sum_congr rfl h, Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Icc,
        nsmul_eq_mul, Nat.add_sub_cancel, ← mul_assoc, mul_one_div_cancel htpos.ne', one_mul,
        ← Finset.mul_sum]
    have hs : slackLP p x (t + 1) = slackLP p x t - p * ∑ σ ∈ Icc 1 t, x t σ := by
      unfold slackLP
      rw [Finset.sum_Ico_succ_top (by omega)]
      ring
    have hp : polD p x y (t + 1) = ∑ σ ∈ Icc 1 t, (y t σ + (1 - p) * x t σ) := by
      unfold polD
      simp only [Nat.add_sub_cancel]
    rw [hs, hp, key, ih (by omega)]
