-- Prove2me | solution 1 for StrictCompatLB.MeanField.lemma_H_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T14:45:54.874834+00:00
-- url     : https://prove2.me/submissions/82a82c49-06b3-47e7-94ba-f632799c8469

import Mathlib
import Definitions.Def_StrictCompatLB_MeanField_Model
import Theorems.Thm_StrictCompatLB_MeanField_lemma_H_2

open Filter Topology MeasureTheory Finset
open scoped ENNReal

open StrictCompatLB.MeanField in
theorem solution (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < 1) (d : ℕ) (hd : 1 ≤ d)
    (M : ℕ → ℕ) (hM : ∀ N, 0 < M N) (G : (N : ℕ) → Finset (Fin N × Fin (M N)))
    (hconn : IsConnectedSeq M G) (hsub : IsSubcritical d M G) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ z : Fin N → ℕ,
      oneStepDrift (jsqdKernel lam d M G N) (lyap 1) z ≤
        -1 + 2 * (CGamma N (3 * ((1 + lam) / (1 - lam)) * (N : ℝ))).indicator
          (fun _ => (1 : ℝ)) z := by
  set ε := (1 - lam) / (3 * lam) with hε
  have hε0 : 0 < ε := div_pos (by linarith) (by linarith)
  obtain ⟨N₀, hN₀, h⟩ := lemma_H_2 lam hlam0 hlam1 d hd M hM G hconn hsub ε hε0
  refine ⟨N₀, hN₀, fun N hN z => ?_⟩
  have hN1 : 1 ≤ N := le_trans hN₀ hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hdr := h N hN 1 le_rfl z
  have hocc : occ z (1 - 1) = 1 := by
    unfold occ Qcount
    simp [hNpos.ne']
  rw [hocc] at hdr
  set a := (1 + ε) * lam with ha
  have ha' : a = lam + (1 - lam) / 3 := by
    rw [ha, hε]; field_simp
  set T := tailSum 1 z with hT
  have hT0 : 0 ≤ T := by
    rw [hT]; unfold tailSum occ
    exact Finset.sum_nonneg (fun _ _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have hl1 : 0 < lam + 1 := by linarith
  by_cases hz : z ∈ CGamma N (3 * ((1 + lam) / (1 - lam)) * (N : ℝ))
  · rw [Set.indicator_of_mem hz]
    have : 1 / (lam + 1) * (a * 1 - (1 - a) * T) ≤ 1 := by
      rw [div_mul_eq_mul_div, one_mul, div_le_one hl1]
      have : 0 ≤ (1 - a) * T := mul_nonneg (by rw [ha']; linarith) hT0
      rw [ha'] at this ⊢; linarith
    linarith
  · rw [Set.indicator_of_notMem hz]
    unfold CGamma at hz
    simp only [Set.mem_setOf_eq, not_le] at hz
    have hTbig : 3 * ((1 + lam) / (1 - lam)) < T := by
      have : T = (∑ i ∈ Ico 1 (maxLen z + 1), (Qcount z i : ℝ)) / N := by
        rw [hT]; unfold tailSum occ; rw [Finset.sum_div]
      rw [this, lt_div_iff₀ hNpos]; exact hz
    have h1a : 1 - a = 2 * (1 - lam) / 3 := by rw [ha']; ring
    have hprod : 2 * (1 + lam) < (1 - a) * T := by
      rw [h1a]
      have h3 : 2 * (1 - lam) / 3 * (3 * ((1 + lam) / (1 - lam))) = 2 * (1 + lam) := by
        have hne : 1 - lam ≠ 0 := by linarith
        field_simp
      have h4 : 0 < 2 * (1 - lam) / 3 := by linarith
      nlinarith
    have : 1 / (lam + 1) * (a * 1 - (1 - a) * T) ≤ -1 := by
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hl1]
      rw [ha'] at hprod ⊢
      nlinarith
    linarith
