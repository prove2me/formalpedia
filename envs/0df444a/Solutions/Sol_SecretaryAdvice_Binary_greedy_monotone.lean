-- Prove2me | solution 1 for SecretaryAdvice.Binary.greedy_monotone
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:43:13.73622+00:00
-- url     : https://prove2.me/submissions/afbec1cc-5905-4346-ab3e-c0b0c851d9d6

import Mathlib
import Definitions.Def_SecretaryAdvice_Binary_LP

set_option autoImplicit false
open SecretaryAdvice.Binary

theorem greedy_stage (n : ℕ) (p p' : ℝ) : ∀ k : ℕ, k ≤ n → ∀ u : ℕ → Bool → ℝ,
    (∀ j, k < j → j ≤ n → ∀ s, u j s = max 0 (a n p s - chat j p' s *
      ∑ l ∈ Finset.Ioc j n, (u l true + u l false))) →
    (∀ j, k < j → ∀ s, (List.range k).reverse.foldl (greedyStep n p p') u j s = u j s) ∧
    (∀ j, 1 ≤ j → j ≤ n → ∀ s, (List.range k).reverse.foldl (greedyStep n p p') u j s =
      max 0 (a n p s - chat j p' s * ∑ l ∈ Finset.Ioc j n,
        ((List.range k).reverse.foldl (greedyStep n p p') u l true +
         (List.range k).reverse.foldl (greedyStep n p p') u l false))) := by
  intro k
  induction k with
  | zero =>
    intro _ u hu
    simp only [List.range_zero, List.reverse_nil, List.foldl_nil]
    exact ⟨by first | trivial | simp, fun j hj hjn s => hu j (by omega) hjn s⟩
  | succ k ih =>
    intro hk u hu
    have hlist : (List.range (k+1)).reverse = k :: (List.range k).reverse := by
      simp [List.range_succ]
    rw [hlist, List.foldl_cons]
    set u' := greedyStep n p p' u k with hu'
    have hu'eq : ∀ j s, u' j s = if j = k + 1 then max 0 (a n p s - chat (k+1) p' s *
        ∑ l ∈ Finset.Ioc (k+1) n, (u l true + u l false)) else u j s := by
      intro j s; rfl
    have hu'ne : ∀ j, j ≠ k + 1 → ∀ s, u' j s = u j s := by
      intro j hj s; rw [hu'eq]; simp [hj]
    have hsum : ∀ j, k + 1 ≤ j → ∑ l ∈ Finset.Ioc j n, (u' l true + u' l false) =
        ∑ l ∈ Finset.Ioc j n, (u l true + u l false) := by
      intro j hj
      apply Finset.sum_congr rfl
      intro l hl
      have : l ≠ k + 1 := by have := (Finset.mem_Ioc.1 hl).1; omega
      rw [hu'ne l this, hu'ne l this]
    have hhyp : ∀ j, k < j → j ≤ n → ∀ s, u' j s = max 0 (a n p s - chat j p' s *
        ∑ l ∈ Finset.Ioc j n, (u' l true + u' l false)) := by
      intro j hj hjn s
      rw [hsum j (by omega)]
      by_cases h : j = k + 1
      · subst h; rw [hu'eq]; simp
      · rw [hu'ne j h]
        exact hu j (by omega) hjn s
    obtain ⟨ih1, ih2⟩ := ih (by omega) u' hhyp
    refine ⟨fun j hj s => ?_, ih2⟩
    rw [ih1 j (by omega), hu'ne j (by omega)]

theorem greedy_rec (n : ℕ) (p p' : ℝ) : ∀ i, 1 ≤ i → i ≤ n → ∀ s,
    greedy n p p' i s = max 0 (a n p s - chat i p' s *
      ∑ l ∈ Finset.Ioc i n, (greedy n p p' l true + greedy n p p' l false)) := by
  have := (greedy_stage n p p' n le_rfl (fun _ _ => 0) (fun j h1 h2 => by omega)).2
  intro i hi hin s
  exact this i hi hin s

theorem greedy_nonneg (n : ℕ) (p p' : ℝ) (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) (s : Bool) :
    0 ≤ greedy n p p' i s := by
  rw [greedy_rec n p p' i hi hin s]; exact le_max_left _ _

theorem tail_nonneg (n : ℕ) (p p' : ℝ) (i : ℕ) :
    0 ≤ ∑ l ∈ Finset.Ioc i n, (greedy n p p' l true + greedy n p p' l false) := by
  apply Finset.sum_nonneg
  intro l hl
  have h := Finset.mem_Ioc.1 hl
  have h1 := greedy_nonneg n p p' l (by omega) h.2 true
  have h2 := greedy_nonneg n p p' l (by omega) h.2 false
  linarith

theorem tail_step (n : ℕ) (p p' : ℝ) (i : ℕ) (hi : i < n) :
    ∑ l ∈ Finset.Ioc i n, (greedy n p p' l true + greedy n p p' l false) =
      (greedy n p p' (i+1) true + greedy n p p' (i+1) false) +
      ∑ l ∈ Finset.Ioc (i+1) n, (greedy n p p' l true + greedy n p p' l false) := by
  rw [← Finset.sum_Ioc_consecutive _ (Nat.le_succ i) (show i + 1 ≤ n by omega),
    Nat.Ioc_succ_singleton, Finset.sum_singleton]

theorem solution (n : ℕ) (hn : 1 ≤ n) (p p' : ℝ)
    (hp0 : (1 / 2 : ℝ) ≤ p) (hp1 : p ≤ 1)
    (hp'0 : (1 / 2 : ℝ) ≤ p') (hp'1 : p' ≤ 1) :
    ∀ i : ℕ, 1 ≤ i → i < n → ∀ s : Bool,
      greedy n p p' i s ≤ greedy n p p' (i + 1) s := by
  intro i hi hin s
  rw [greedy_rec n p p' i hi hin.le s, greedy_rec n p p' (i+1) (by omega) (by omega) s]
  apply max_le_max le_rfl
  have hT := tail_step n p p' i hin
  have hT1 := tail_nonneg n p p' (i+1)
  have hg1 := greedy_nonneg n p p' (i+1) (by omega) (by omega) true
  have hg2 := greedy_nonneg n p p' (i+1) (by omega) (by omega) false
  have hκ : 0 ≤ (if s then 1 - p' else p') := by split_ifs <;> linarith
  have hi' : (0 : ℝ) < i := by exact_mod_cast hi
  have hcc : chat (i+1) p' s ≤ chat i p' s := by
    unfold chat
    apply div_le_div_of_nonneg_left hκ hi'
    push_cast; linarith
  have hc0 : 0 ≤ chat (i+1) p' s := by
    unfold chat; positivity
  have hmul : chat (i+1) p' s * ∑ l ∈ Finset.Ioc (i+1) n, (greedy n p p' l true + greedy n p p' l false) ≤
      chat i p' s * ∑ l ∈ Finset.Ioc i n, (greedy n p p' l true + greedy n p p' l false) := by
    apply mul_le_mul hcc (by linarith) hT1 (hc0.trans hcc)
  linarith
