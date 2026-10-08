-- Prove2me | solution 1 for UniformPrecSched.Makespan.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T19:04:22.785072+00:00
-- url     : https://prove2.me/submissions/3a843ec7-10e7-4503-8b5e-140f21a38fb8

import Mathlib
import Definitions.Def_UniformPrecSched_Makespan_Model
import Definitions.Def_UniformPrecSched_Makespan_LP

set_option autoImplicit false

namespace UniformPrecSched.Makespan.L31Aux

open UniformPrecSched.Makespan

theorem classSpeed_pos {n m : ℕ} (I : Instance n m) (κ : Fin (numSpeeds I)) :
    0 < classSpeed I κ := by
  have h : classSpeed I κ ∈ speedSet I := by
    unfold classSpeed; exact Finset.orderEmbOfFin_mem _ _ _
  simp only [speedSet, Finset.mem_image, Finset.mem_univ, true_and] at h
  obtain ⟨i, hi⟩ := h
  rw [← hi]; exact I.s_pos i

theorem pbar_pos {n m : ℕ} (I : Instance n m) (x : Fin (numSpeeds I) → Fin n → ℝ)
    (C : Fin n → ℝ) (D : ℝ) (hLP : LPFeasible I x C D) (j : Fin n) :
    0 < pbar I x j := by
  obtain ⟨h1, -, -, -, -, h8⟩ := hLP
  have hex : ∃ κ, 0 < x κ j := by
    by_contra hcon
    push_neg at hcon
    have : ∑ κ, x κ j ≤ 0 := Finset.sum_nonpos (fun κ _ => hcon κ)
    rw [h1 j] at this; norm_num at this
  obtain ⟨κ0, hκ0⟩ := hex
  unfold pbar
  apply Finset.sum_pos'
  · intro κ _
    exact mul_nonneg (div_nonneg (I.p_pos j).le (classSpeed_pos I κ).le) (h8 κ j)
  · exact ⟨κ0, Finset.mem_univ _,
      mul_pos (div_pos (I.p_pos j) (classSpeed_pos I κ0)) hκ0⟩

theorem compl_nonempty {n m : ℕ} (I : Instance n m) (x : Fin (numSpeeds I) → Fin n → ℝ)
    (C : Fin n → ℝ) (D : ℝ) (hLP : LPFeasible I x C D) (j : Fin n) :
    ∃ κ, κ ∉ badSet I x 2 j := by
  have hp := pbar_pos I x C D hLP j
  obtain ⟨h1, -, -, -, -, h8⟩ := hLP
  by_contra hcon
  push_neg at hcon
  have hex : ∃ κ, 0 < x κ j := by
    by_contra hc
    push_neg at hc
    have : ∑ κ, x κ j ≤ 0 := Finset.sum_nonpos (fun κ _ => hc κ)
    rw [h1 j] at this; norm_num at this
  obtain ⟨κ0, hκ0⟩ := hex
  have hlt : ∑ κ, (2 * pbar I x j) * x κ j < ∑ κ, I.p j / classSpeed I κ * x κ j := by
    apply Finset.sum_lt_sum
    · intro κ _
      have hb := hcon κ
      simp only [badSet, Finset.mem_filter, Finset.mem_univ, true_and] at hb
      exact mul_le_mul_of_nonneg_right hb.le (h8 κ j)
    · refine ⟨κ0, Finset.mem_univ _, ?_⟩
      have hb := hcon κ0
      simp only [badSet, Finset.mem_filter, Finset.mem_univ, true_and] at hb
      exact mul_lt_mul_of_pos_right hb hκ0
  rw [← Finset.mul_sum, h1 j] at hlt
  change 2 * pbar I x j * 1 < pbar I x j at hlt
  linarith

theorem chain_sum {n m : ℕ} (I : Instance n m) (x : Fin (numSpeeds I) → Fin n → ℝ)
    (C : Fin n → ℝ) (D : ℝ) (hLP : LPFeasible I x C D) :
    ∀ (N : ℕ) (c : Finset (Fin n)), c.card = N → IsJobChain I c → c.Nonempty →
      ∃ t ∈ c, ∑ j ∈ c, pbar I x j ≤ C t := by
  have hpos := pbar_pos I x C D hLP
  obtain ⟨-, -, h3, h4, -, -⟩ := hLP
  intro N
  induction N with
  | zero =>
    intro c hc _ hne
    exact absurd (Finset.card_pos.mpr hne) (by omega)
  | succ N ih =>
    intro c hc hch hne
    obtain ⟨t, ht, hmax⟩ := Finset.exists_max_image c C hne
    have hbelow : ∀ j ∈ c.erase t, I.prec j t := by
      intro j hj
      have hjt : j ≠ t := Finset.ne_of_mem_erase hj
      have hjc : j ∈ c := Finset.mem_of_mem_erase hj
      rcases hch hjc ht hjt with h | h
      · exact h
      · exfalso
        have := h4 t j h
        have hj := hmax j hjc
        have hp := hpos j
        change pbar I x j ≤ C j - C t at this
        linarith
    have hsum : ∑ j ∈ c, pbar I x j = pbar I x t + ∑ j ∈ c.erase t, pbar I x j :=
      (Finset.add_sum_erase c _ ht).symm
    refine ⟨t, ht, ?_⟩
    rw [hsum]
    rcases (c.erase t).eq_empty_or_nonempty with he | he
    · rw [he, Finset.sum_empty, add_zero]
      exact h3 t
    · have hcard : (c.erase t).card = N := by
        rw [Finset.card_erase_of_mem ht, hc]; rfl
      have hch' : IsJobChain I (c.erase t) := by
        unfold IsJobChain at hch ⊢
        exact hch.mono (by intro y hy; exact Finset.mem_of_mem_erase hy)
      obtain ⟨t', ht', hle⟩ := ih (c.erase t) hcard hch' he
      have := h4 t' t (hbelow t' ht')
      change pbar I x t ≤ C t - C t' at this
      linarith

theorem D_nonneg {n m : ℕ} (I : Instance n m) (x : Fin (numSpeeds I) → Fin n → ℝ)
    (C : Fin n → ℝ) (D : ℝ) (hLP : LPFeasible I x C D) : 0 ≤ D := by
  obtain ⟨-, h2, -, -, -, h8⟩ := hLP
  have hK : 0 < numSpeeds I := by
    unfold numSpeeds speedSet
    apply Finset.card_pos.mpr
    exact ⟨I.s ⟨0, I.m_pos⟩, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
  have h := h2 ⟨0, hK⟩
  refine le_trans ?_ h
  apply mul_nonneg
  · apply div_nonneg zero_le_one
    exact mul_nonneg (Nat.cast_nonneg _) (classSpeed_pos I _).le
  · exact Finset.sum_nonneg (fun j _ => mul_nonneg (I.p_pos j).le (h8 _ j))

end UniformPrecSched.Makespan.L31Aux

open UniformPrecSched.Makespan in
theorem solution {n m : ℕ} (I : Instance n m) (x : Fin (numSpeeds I) → Fin n → ℝ)
    (C : Fin n → ℝ) (D : ℝ) (hLP : LPFeasible I x C D) :
    (∃ k, IsLPAssignment I x 2 k) ∧
      ∀ k, IsLPAssignment I x 2 k → ∀ c, IsJobChain I c → chainLength I k c ≤ 2 * D := by
  classical
  constructor
  · have hsel : ∀ j, ∃ κ, κ ∉ badSet I x 2 j ∧ ∀ κ' ∉ badSet I x 2 j,
        classSpeed I κ' * (classCount I κ' : ℝ) ≤ classSpeed I κ * (classCount I κ : ℝ) := by
      intro j
      obtain ⟨κ1, hκ1⟩ := L31Aux.compl_nonempty I x C D hLP j
      have hne : (Finset.univ.filter fun κ => κ ∉ badSet I x 2 j).Nonempty :=
        ⟨κ1, by simp [hκ1]⟩
      obtain ⟨κ, hκ, hmax⟩ := Finset.exists_max_image _
        (fun κ => classSpeed I κ * (classCount I κ : ℝ)) hne
      refine ⟨κ, by simpa using hκ, ?_⟩
      intro κ' hκ'
      exact hmax κ' (by simp [hκ'])
    choose k hk using hsel
    exact ⟨k, fun j => hk j⟩
  · intro k hk c hc
    have hD := L31Aux.D_nonneg I x C D hLP
    have hterm : ∀ j ∈ c, I.p j / classSpeed I (k j) ≤ 2 * pbar I x j := by
      intro j _
      have h := (hk j).1
      simp only [badSet, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at h
      exact h
    have hle : chainLength I k c ≤ 2 * ∑ j ∈ c, pbar I x j := by
      unfold chainLength
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum hterm
    rcases c.eq_empty_or_nonempty with he | he
    · subst he
      simp [chainLength]
      exact hD
    · obtain ⟨t, _, hsum⟩ := L31Aux.chain_sum I x C D hLP c.card c rfl hc he
      have h5 := hLP.2.2.2.2.1 t
      linarith
