-- Prove2me | solution 1 for ScenarioReduction.BinaryTree.redCost_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T19:21:00.471691+00:00
-- url     : https://prove2.me/submissions/26b92def-40e5-4cce-bf9d-24305e87616b

import Mathlib
import Definitions.Def_ScenarioReduction_BinaryTree_redCost



namespace ScenarioReduction.BinaryTree

open Finset

variable {K : ℕ}

lemma scen_sub (δ : ℕ → ℝ) (σ τ : Fin K → Fin 2) (k : Fin (K + 1)) :
    (scenario δ σ - scenario δ τ) k =
      ∑ r ∈ Icc 1 k.val, 2 * (((lev σ r).val : ℝ) - (lev τ r).val) * δ r := by
  simp only [Pi.sub_apply, scenario, ← sum_sub_distrib]
  apply sum_congr rfl; intro r _; ring

lemma fin2_abs {a b : Fin 2} (h : a ≠ b) : |((a.val : ℝ) - b.val)| = 1 := by
  fin_cases a <;> fin_cases b <;> simp_all

lemma coord_first_diff (δ : ℕ → ℝ) (σ τ : Fin K → Fin 2) (l : ℕ) (hl : l ∈ Icc 1 K)
    (hdiff : lev σ l ≠ lev τ l) (hagree : ∀ r ∈ Icc 1 (l - 1), lev σ r = lev τ r)
    (hδ : 0 ≤ δ l) :
    |(scenario δ σ - scenario δ τ) ⟨l, by rw [mem_Icc] at hl; omega⟩| = 2 * δ l := by
  rw [scen_sub]
  rw [sum_eq_single_of_mem l (by rw [mem_Icc] at hl ⊢; simp; omega)]
  · rw [abs_mul, abs_mul, fin2_abs hdiff, abs_of_nonneg hδ]; norm_num
  · intro r hr hrl
    simp only [mem_Icc] at hr
    rw [hagree r (by rw [mem_Icc]; omega)]; ring

theorem distance_bound (K : ℕ) (δ : ℕ → ℝ) (hδ : ∀ k ∈ Finset.Icc 1 K, 0 ≤ δ k)
    (k0 : ℕ) (hk0 : k0 ∈ Finset.Icc 1 K) (hmin : ∀ k ∈ Finset.Icc 1 K, δ k0 ≤ δ k)
    (σ τ : Fin K → Fin 2) (l : ℕ) (hl : l ∈ Finset.Icc 1 K) (hdiff : lev σ l ≠ lev τ l)
    (hagree : ∀ r ∈ Finset.Icc 1 (l - 1), lev σ r = lev τ r) :
    2 * δ l ≤ ‖scenario δ σ - scenario δ τ‖ ∧ 2 * δ k0 ≤ ‖scenario δ σ - scenario δ τ‖ := by
  have h1 := coord_first_diff δ σ τ l hl hdiff hagree (hδ l hl)
  have h2 := norm_le_pi_norm (scenario δ σ - scenario δ τ) ⟨l, by rw [mem_Icc] at hl; omega⟩
  rw [Real.norm_eq_abs, h1] at h2
  exact ⟨h2, by linarith [hmin l hl]⟩

lemma exists_first_diff (σ τ : Fin K → Fin 2) (h : σ ≠ τ) :
    ∃ l ∈ Icc 1 K, lev σ l ≠ lev τ l ∧ ∀ r ∈ Icc 1 (l - 1), lev σ r = lev τ r := by
  have hex : ∃ m, ∃ hm : m < K, σ ⟨m, hm⟩ ≠ τ ⟨m, hm⟩ := by
    by_contra hc; push_neg at hc; exact h (funext fun i => hc i.val i.isLt)
  classical
  let m := Nat.find hex
  obtain ⟨hm, hne⟩ := Nat.find_spec hex
  refine ⟨m + 1, by rw [mem_Icc]; omega, ?_, ?_⟩
  · unfold lev; rw [dif_pos (by omega), dif_pos (by omega)]; simpa using hne
  · intro r hr
    rw [mem_Icc] at hr
    unfold lev; rw [dif_pos (by omega), dif_pos (by omega)]
    have := Nat.find_min hex (show r - 1 < m by omega)
    push_neg at this; exact this (by omega)

lemma sep (K : ℕ) (δ : ℕ → ℝ) (hδ : ∀ k ∈ Finset.Icc 1 K, 0 ≤ δ k)
    (k0 : ℕ) (hk0 : k0 ∈ Finset.Icc 1 K) (hmin : ∀ k ∈ Finset.Icc 1 K, δ k0 ≤ δ k)
    (σ τ : Fin K → Fin 2) (h : σ ≠ τ) : 2 * δ k0 ≤ ‖scenario δ σ - scenario δ τ‖ := by
  obtain ⟨l, hl, hd, ha⟩ := exists_first_diff σ τ h
  exact (distance_bound K δ hδ k0 hk0 hmin σ τ l hl hd ha).2

theorem redCost_lower_bound (K : ℕ) (δ : ℕ → ℝ) (hδ : ∀ k ∈ Finset.Icc 1 K, 0 ≤ δ k)
    (k0 : ℕ) (hk0 : k0 ∈ Finset.Icc 1 K) (hmin : ∀ k ∈ Finset.Icc 1 K, δ k0 ≤ δ k)
    (n : ℕ) (hn : n < 2 ^ K) (J : Finset (Fin K → Fin 2)) (hJcard : J.card = 2 ^ K - n)
    (hJ : Jᶜ.Nonempty) :
    ((2 : ℝ) ^ K - n) / 2 ^ K * (2 * δ k0) ≤ redCost δ J hJ := by
  unfold redCost
  have hterm : ∀ σ ∈ J, (1 / (2 ^ K : ℝ)) * (2 * δ k0) ≤
      (1 / (2 ^ K : ℝ)) * Jᶜ.inf' hJ (fun τ => ‖scenario δ σ - scenario δ τ‖) := by
    intro σ hσ
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply le_inf'; intro τ hτ
    apply sep K δ hδ k0 hk0 hmin
    rintro rfl; rw [mem_compl] at hτ; exact hτ hσ
  refine le_trans ?_ (sum_le_sum hterm)
  rw [sum_const, hJcard, nsmul_eq_mul, Nat.cast_sub hn.le]; push_cast
  apply le_of_eq; ring

end ScenarioReduction.BinaryTree

open ScenarioReduction.BinaryTree

theorem solution (K : ℕ) (δ : ℕ → ℝ) (hδ : ∀ k ∈ Finset.Icc 1 K, 0 ≤ δ k)
    (k0 : ℕ) (hk0 : k0 ∈ Finset.Icc 1 K) (hmin : ∀ k ∈ Finset.Icc 1 K, δ k0 ≤ δ k)
    (n : ℕ) (hn : n < 2 ^ K) (J : Finset (Fin K → Fin 2)) (hJcard : J.card = 2 ^ K - n)
    (hJ : Jᶜ.Nonempty) :
    ((2 : ℝ) ^ K - n) / 2 ^ K * (2 * δ k0) ≤ redCost δ J hJ := by
  exact redCost_lower_bound K δ hδ k0 hk0 hmin n hn J hJcard hJ
