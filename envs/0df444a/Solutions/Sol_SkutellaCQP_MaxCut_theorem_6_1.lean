-- Prove2me | solution 1 for SkutellaCQP.MaxCut.theorem_6_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T09:38:54.262417+00:00
-- url     : https://prove2.me/submissions/308f1670-1493-47fd-963f-2f6a2b6c51d8

import Mathlib
import Definitions.Def_SkutellaCQP_MaxCut_Setting

set_option autoImplicit false

namespace SkutCQPAux98f

open Finset SkutellaCQP.MaxCut

theorem prec_irrefl {n : ℕ} (p w : Fin n → ℝ) (a : Fin n) : ¬ prec p w a a := by
  unfold prec
  rintro (h | ⟨_, h⟩)
  · exact lt_irrefl _ h
  · exact lt_irrefl _ h

theorem prec_asymm {n : ℕ} (p w : Fin n → ℝ) (a b : Fin n) (h1 : prec p w a b) :
    ¬ prec p w b a := by
  unfold prec at *
  rintro h2
  rcases h1 with h1 | ⟨h1, h1'⟩ <;> rcases h2 with h2 | ⟨h2, h2'⟩
  · linarith
  · linarith
  · linarith
  · exact lt_asymm h1' h2'

theorem prec_le {n : ℕ} (p w : Fin n → ℝ) (a b : Fin n) (h : prec p w a b) :
    w b * p a ≤ w a * p b := by
  unfold prec at h
  rcases h with h | ⟨h, _⟩
  · linarith
  · linarith

theorem prec_total {n : ℕ} (p w : Fin n → ℝ) (a b : Fin n) (hab : a ≠ b) :
    prec p w a b ∨ prec p w b a := by
  unfold prec
  rcases lt_trichotomy (w a * p b) (w b * p a) with h | h | h
  · right; left; linarith
  · rcases lt_or_gt_of_ne hab with h' | h'
    · left; right; exact ⟨h, h'⟩
    · right; right; exact ⟨h.symm, h'⟩
  · left; left; linarith

theorem prec_trans {n : ℕ} (p w : Fin n → ℝ) (hp : ∀ j, 0 < p j) {a b c : Fin n}
    (h1 : prec p w a b) (h2 : prec p w b c) : prec p w a c := by
  unfold prec at *
  have key : p b * (w a * p c - w c * p a) =
      p c * (w a * p b - w b * p a) + p a * (w b * p c - w c * p b) := by ring
  have hpa := hp a
  have hpb := hp b
  have hpc := hp c
  rcases h1 with h1 | ⟨h1, h1'⟩ <;> rcases h2 with h2 | ⟨h2, h2'⟩
  · left
    have e1 : 0 < p c * (w a * p b - w b * p a) := mul_pos hpc (by linarith)
    have e2 : 0 < p a * (w b * p c - w c * p b) := mul_pos hpa (by linarith)
    by_contra hc
    push Not at hc
    have : p b * (w a * p c - w c * p a) ≤ p b * 0 :=
      mul_le_mul_of_nonneg_left (by linarith) hpb.le
    linarith
  · left
    have e1 : 0 < p c * (w a * p b - w b * p a) := mul_pos hpc (by linarith)
    have e2 : p a * (w b * p c - w c * p b) = 0 := by rw [h2]; ring
    by_contra hc
    push Not at hc
    have : p b * (w a * p c - w c * p a) ≤ p b * 0 :=
      mul_le_mul_of_nonneg_left (by linarith) hpb.le
    linarith
  · left
    have e1 : p c * (w a * p b - w b * p a) = 0 := by rw [h1]; ring
    have e2 : 0 < p a * (w b * p c - w c * p b) := mul_pos hpa (by linarith)
    by_contra hc
    push Not at hc
    have : p b * (w a * p c - w c * p a) ≤ p b * 0 :=
      mul_le_mul_of_nonneg_left (by linarith) hpb.le
    linarith
  · right
    refine ⟨?_, lt_trans h1' h2'⟩
    have e1 : p c * (w a * p b - w b * p a) = 0 := by rw [h1]; ring
    have e2 : p a * (w b * p c - w c * p b) = 0 := by rw [h2]; ring
    have h0 : p b * (w a * p c - w c * p a) = 0 := by rw [key, e1, e2]; ring
    rcases mul_eq_zero.1 h0 with h | h
    · exact absurd h hpb.ne'
    · linarith

theorem compl_nonneg {m n : ℕ} (p w : Fin n → ℝ) (hp : ∀ j, 0 < p j) (τ : Fin n → Fin m)
    (j : Fin n) : 0 ≤ compl p w τ j := by
  unfold SkutellaCQP.MaxCut.compl
  have := hp j
  have : 0 ≤ ∑ k ∈ univ.filter (fun k => prec p w k j ∧ τ k = τ j), p k :=
    Finset.sum_nonneg (fun k _ => (hp k).le)
  linarith

theorem compl_lt {m n : ℕ} (p w : Fin n → ℝ) (hp : ∀ j, 0 < p j) (τ : Fin n → Fin m)
    (a b : Fin n) (hab : prec p w a b) (hτ : τ a = τ b) :
    compl p w τ a < compl p w τ b := by
  unfold SkutellaCQP.MaxCut.compl
  have hsub : insert a (univ.filter (fun k => prec p w k a ∧ τ k = τ a)) ⊆
      univ.filter (fun k => prec p w k b ∧ τ k = τ b) := by
    intro x hx
    rw [Finset.mem_insert] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rcases hx with rfl | ⟨h1, h2⟩
    · exact ⟨hab, hτ⟩
    · exact ⟨prec_trans p w hp h1 hab, h2.trans hτ⟩
  have hnot : a ∉ univ.filter (fun k => prec p w k a ∧ τ k = τ a) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and]
    intro h; exact absurd h (prec_irrefl p w a)
  have h1 := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => (hp k).le)
  rw [Finset.sum_insert hnot] at h1
  have := hp b
  linarith

theorem machine_le {m n : ℕ} (p w : Fin n → ℝ) (hp : ∀ j, 0 < p j) (τ : Fin n → Fin m)
    (i : Fin m) (j : Fin n) :
    ∑ k ∈ (univ.filter (fun k => τ k = i)).filter
        (fun k => compl p w τ k ≤ compl p w τ j), p k ≤ compl p w τ j := by
  set T := (univ.filter (fun k => τ k = i)).filter
        (fun k => compl p w τ k ≤ compl p w τ j) with hT
  rcases T.eq_empty_or_nonempty with he | hne
  · rw [he, Finset.sum_empty]; exact compl_nonneg p w hp τ j
  obtain ⟨s, hs, hmax⟩ := Finset.exists_max_image T (compl p w τ) hne
  have hs' := hs
  rw [hT] at hs'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs'
  have hsub : T ⊆ insert s (univ.filter (fun k => prec p w k s ∧ τ k = τ s)) := by
    intro x hx
    have hx' := hx
    rw [hT] at hx'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx'
    rw [Finset.mem_insert]
    by_cases hxs : x = s
    · left; exact hxs
    · right
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨?_, hx'.1.trans hs'.1.symm⟩
      rcases prec_total p w x s hxs with h | h
      · exact h
      · exfalso
        have := compl_lt p w hp τ s x h (hs'.1.trans hx'.1.symm)
        have := hmax x hx
        linarith
  have hnot : s ∉ univ.filter (fun k => prec p w k s ∧ τ k = τ s) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and]
    intro h; exact absurd h (prec_irrefl p w s)
  have h1 := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => (hp k).le)
  rw [Finset.sum_insert hnot] at h1
  have h2 : p s + ∑ k ∈ univ.filter (fun k => prec p w k s ∧ τ k = τ s), p k
      = compl p w τ s := rfl
  linarith [hs'.2]

theorem total_le {m n : ℕ} (p w : Fin n → ℝ) (hp : ∀ j, 0 < p j) (τ : Fin n → Fin m)
    (j : Fin n) :
    ∑ k, (if compl p w τ k ≤ compl p w τ j then p k else 0) ≤ (m : ℝ) * compl p w τ j := by
  rw [← Finset.sum_fiberwise univ τ]
  have : ∀ i : Fin m, ∑ k ∈ univ.filter (fun k => τ k = i),
      (if compl p w τ k ≤ compl p w τ j then p k else 0) ≤ compl p w τ j := by
    intro i
    rw [← Finset.sum_filter]
    exact machine_le p w hp τ i j
  calc _ ≤ ∑ _i : Fin m, compl p w τ j := Finset.sum_le_sum (fun i _ => this i)
    _ = _ := by simp

theorem pair_le {m n : ℕ} (p w : Fin n → ℝ) (hp : ∀ j, 0 < p j) (hw : ∀ j, 0 ≤ w j)
    (τ : Fin n → Fin m) (j k : Fin n) :
    (edgeW p w j k + if j = k then w j * p j else 0) +
      (edgeW p w k j + if k = j then w k * p k else 0) ≤
    (if compl p w τ k ≤ compl p w τ j then w j * p k else 0) +
      (if compl p w τ j ≤ compl p w τ k then w k * p j else 0) := by
  have g1 : 0 ≤ (if compl p w τ k ≤ compl p w τ j then w j * p k else 0) := by
    split_ifs
    · exact mul_nonneg (hw j) (hp k).le
    · exact le_refl _
  have g2 : 0 ≤ (if compl p w τ j ≤ compl p w τ k then w k * p j else 0) := by
    split_ifs
    · exact mul_nonneg (hw k) (hp j).le
    · exact le_refl _
  by_cases hjk : j = k
  · subst hjk
    have e : edgeW p w j j = 0 := by
      unfold edgeW; rw [if_neg (prec_irrefl p w j)]
    simp only [e, if_true, le_refl, zero_add]
  · have hkj : k ≠ j := fun h => hjk h.symm
    simp only [hjk, hkj, if_false, add_zero]
    rcases prec_total p w j k hjk with h | h
    · -- j ≺ k : edge (k, j) has weight w k * p j
      have e1 : edgeW p w j k = 0 := by
        unfold edgeW; rw [if_neg (prec_asymm p w j k h)]
      have e2 : edgeW p w k j = w k * p j := by
        unfold edgeW; rw [if_pos h]
      have hle := prec_le p w j k h
      rw [e1, e2]
      by_cases hc : compl p w τ j ≤ compl p w τ k
      · rw [if_pos hc] at g2 ⊢; linarith
      · have hc' : compl p w τ k ≤ compl p w τ j := le_of_lt (not_le.1 hc)
        rw [if_pos hc'] at g1 ⊢; linarith
    · have e1 : edgeW p w k j = 0 := by
        unfold edgeW; rw [if_neg (prec_asymm p w k j h)]
      have e2 : edgeW p w j k = w j * p k := by
        unfold edgeW; rw [if_pos h]
      have hle := prec_le p w k j h
      rw [e1, e2]
      by_cases hc : compl p w τ k ≤ compl p w τ j
      · rw [if_pos hc] at g1 ⊢; linarith
      · have hc' : compl p w τ j ≤ compl p w τ k := le_of_lt (not_le.1 hc)
        rw [if_pos hc'] at g2 ⊢; linarith

theorem sym_le {n : ℕ} (h g : Fin n → Fin n → ℝ) (H : ∀ j k, h j k + h k j ≤ g j k + g k j) :
    ∑ j, ∑ k, h j k ≤ ∑ j, ∑ k, g j k := by
  have e1 : ∑ j, ∑ k, h k j = ∑ j, ∑ k, h j k := Finset.sum_comm
  have e2 : ∑ j, ∑ k, g k j = ∑ j, ∑ k, g j k := Finset.sum_comm
  have : ∑ j, ∑ k, (h j k + h k j) ≤ ∑ j, ∑ k, (g j k + g k j) :=
    Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun k _ => H j k))
  simp only [Finset.sum_add_distrib] at this
  linarith

theorem key_le {m n : ℕ} (p w : Fin n → ℝ) (hp : ∀ j, 0 < p j) (hw : ∀ j, 0 ≤ w j)
    (τ : Fin n → Fin m) :
    (∑ j, w j * p j) + cE p w ≤ (m : ℝ) * val p w τ := by
  have hL : (∑ j, w j * p j) + cE p w =
      ∑ j, ∑ k, (edgeW p w j k + if j = k then w j * p j else 0) := by
    unfold cE
    simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    ring
  have hR : ∑ j, ∑ k, (if compl p w τ k ≤ compl p w τ j then w j * p k else 0) ≤
      (m : ℝ) * val p w τ := by
    unfold SkutellaCQP.MaxCut.val
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    have h1 := total_le p w hp τ j
    have h2 : ∑ k, (if compl p w τ k ≤ compl p w τ j then w j * p k else 0) =
        w j * ∑ k, (if compl p w τ k ≤ compl p w τ j then p k else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      split_ifs <;> ring
    rw [h2]
    have := mul_le_mul_of_nonneg_left h1 (hw j)
    linarith
  rw [hL]
  exact le_trans (sym_le _ _ (fun j k => pair_le p w hp hw τ j k)) hR

theorem val_add_cut {m n : ℕ} (p w : Fin n → ℝ) (τ : Fin n → Fin m) :
    val p w τ + cut p w τ = (∑ j, w j * p j) + cE p w := by
  unfold SkutellaCQP.MaxCut.val SkutellaCQP.MaxCut.compl cut cE
  simp only [mul_add, Finset.mul_sum, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [add_assoc]
  congr 1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  unfold edgeW
  by_cases h1 : prec p w k j <;> by_cases h2 : τ k = τ j <;>
    simp [h1, h2, show (τ j = τ k) ↔ (τ k = τ j) from eq_comm]

end SkutCQPAux98f

open SkutellaCQP.MaxCut Finset in
theorem solution {m n : ℕ} (p w : Fin n → ℝ) (hp : ∀ j, 0 < p j) (hw : ∀ j, 0 ≤ w j)
    (hm : 0 < m) (ρ : ℝ) (hρ : ρ ≤ 1) (σ : Fin n → Fin m)
    (hσ : ∀ τ : Fin n → Fin m, ρ * cut p w τ ≤ cut p w σ) :
    ∀ τ : Fin n → Fin m, val p w σ ≤ (ρ + m * (1 - ρ)) * val p w τ := by
  intro τ
  have e1 := SkutCQPAux98f.val_add_cut p w σ
  have e2 := SkutCQPAux98f.val_add_cut p w τ
  have k := SkutCQPAux98f.key_le p w hp hw τ
  have h := hσ τ
  nlinarith [mul_nonneg (sub_nonneg.2 hρ)
    (sub_nonneg.2 k)]
