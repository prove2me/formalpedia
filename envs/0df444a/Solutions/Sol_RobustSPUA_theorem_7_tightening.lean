-- Prove2me | solution 1 for RobustSPUA.theorem_7_tightening
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T00:02:10.623171+00:00
-- url     : https://prove2.me/submissions/b46630e8-7ef6-4962-b950-83c546989b1a

import Mathlib
import Definitions.Def_RobustSPUA_Model
import Definitions.Def_RobustSPUA_LP

open Finset

namespace RobustSPUA.Aux_RS

open RobustSPUA

noncomputable def Yf (p : ℝ) (x : ℕ → ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0 => fun _ => 0
  | 1 => fun _ => 1 - x 1 1
  | (t + 2) => fun s =>
      (1 / ((t + 2 : ℕ) : ℝ)) * ∑ σ ∈ Icc 1 (t + 1), (Yf p x (t + 1) σ + (1 - p) * x (t + 1) σ)
        - x (t + 2) s

theorem Yf_one (p : ℝ) (x : ℕ → ℕ → ℝ) (s : ℕ) : Yf p x 1 s = 1 - x 1 1 := by
  simp [Yf]

theorem Yf_succ (p : ℝ) (x : ℕ → ℕ → ℝ) (t s : ℕ) :
    Yf p x (t + 2) s = (1 / ((t + 2 : ℕ) : ℝ)) *
      ∑ σ ∈ Icc 1 (t + 1), (Yf p x (t + 1) σ + (1 - p) * x (t + 1) σ) - x (t + 2) s := by
  simp [Yf]

theorem polD_succ (p : ℝ) (x y : ℕ → ℕ → ℝ) (t : ℕ) :
    polD p x y (t + 2) = ∑ σ ∈ Icc 1 (t + 1), (y (t + 1) σ + (1 - p) * x (t + 1) σ) := by
  simp only [polD, show t + 2 - 1 = t + 1 from rfl]

theorem mono (n : ℕ) (p : ℝ) (x y : ℕ → ℕ → ℝ) (hxy : POLineq n p x y) :
    ∀ k, k + 1 ≤ n → ∀ s ∈ Icc 1 (k + 1), y (k + 1) s ≤ Yf p x (k + 1) s := by
  intro k
  induction k with
  | zero =>
    intro hn s hs
    have hs1 : s = 1 := by simp only [Finset.mem_Icc] at hs; omega
    subst hs1
    rw [Yf_one]
    linarith [hxy.2.1]
  | succ k ih =>
    intro hn s hs
    have h := hxy.2.2 (k + 2) (by simp only [Finset.mem_Icc]; omega) s hs
    rw [polD_succ] at h
    rw [Yf_succ]
    have hsum : ∑ σ ∈ Icc 1 (k + 1), (y (k + 1) σ + (1 - p) * x (k + 1) σ) ≤
        ∑ σ ∈ Icc 1 (k + 1), (Yf p x (k + 1) σ + (1 - p) * x (k + 1) σ) := by
      apply Finset.sum_le_sum
      intro σ hσ
      have := ih (by omega) σ hσ
      linarith
    have hc : (0 : ℝ) ≤ 1 / ((k + 2 : ℕ) : ℝ) := by positivity
    have := mul_le_mul_of_nonneg_left hsum hc
    linarith

end RobustSPUA.Aux_RS

open RobustSPUA RobustSPUA.Aux_RS in
theorem solution (n : ℕ) (hn : 1 ≤ n) (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (x y : ℕ → ℕ → ℝ) (hxy : POLineq n p x y) :
    ∃ y' : ℕ → ℕ → ℝ, (∀ t ∈ Icc 1 n, ∀ s ∈ Icc 1 t, y t s ≤ y' t s) ∧ POL n p x y' := by
  have hmono : ∀ t ∈ Icc 1 n, ∀ s ∈ Icc 1 t, y t s ≤ Yf p x t s := by
    intro t ht s hs
    simp only [Finset.mem_Icc] at ht
    obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
    exact mono n p x y hxy k ht.2 s hs
  refine ⟨Yf p x, hmono, ?_, ?_, ?_⟩
  · intro t ht s hs
    have h0 := hxy.1 t ht s hs
    exact ⟨h0.1, le_trans h0.2 (hmono t ht s hs)⟩
  · rw [Yf_one]; ring
  · intro t ht s hs
    simp only [Finset.mem_Icc] at ht
    obtain ⟨k, rfl⟩ : ∃ k, t = k + 2 := ⟨t - 2, by omega⟩
    rw [Yf_succ, polD_succ]
    ring
