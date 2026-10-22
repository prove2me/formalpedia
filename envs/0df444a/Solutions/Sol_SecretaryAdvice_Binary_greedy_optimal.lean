-- Prove2me | solution 1 for SecretaryAdvice.Binary.greedy_optimal
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:43:18.276889+00:00
-- url     : https://prove2.me/submissions/ccdec7fa-fdae-4be5-a15f-6bdfda2303f0

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

theorem sum_Ioc_step (f : ℕ → ℝ) (n i : ℕ) (hi : i < n) :
    ∑ l ∈ Finset.Ioc i n, f l = f (i+1) + ∑ l ∈ Finset.Ioc (i+1) n, f l := by
  rw [← Finset.sum_Ioc_consecutive _ (Nat.le_succ i) (show i + 1 ≤ n by omega),
    Nat.Ioc_succ_singleton, Finset.sum_singleton]

theorem solution (n : ℕ) (hn : 1 ≤ n) (p p' : ℝ)
    (hp0 : (1 / 2 : ℝ) ≤ p) (hp1 : p ≤ 1)
    (hp'0 : (1 / 2 : ℝ) ≤ p') (hp'1 : p' ≤ 1) :
    DualFeasible n p p' (greedy n p p') ∧
    ∀ u : ℕ → Bool → ℝ, DualFeasible n p p' u →
      dualValue n (greedy n p p') ≤ dualValue n u := by
  constructor
  · intro i hi hin s
    refine ⟨greedy_nonneg n p p' i hi hin s, ?_⟩
    have h1 := greedy_rec n p p' i hi hin s
    have h2 := le_max_right 0 (a n p s - chat i p' s *
      ∑ l ∈ Finset.Ioc i n, (greedy n p p' l true + greedy n p p' l false))
    rw [← h1] at h2
    linarith
  · intro v hv
    have key : ∀ k : ℕ, k ≤ n →
        ∑ l ∈ Finset.Ioc (n - k) n, (greedy n p p' l true + greedy n p p' l false) ≤
        ∑ l ∈ Finset.Ioc (n - k) n, (v l true + v l false) := by
      intro k
      induction k with
      | zero => intro _; rw [Nat.sub_zero, Finset.Ioc_self]; simp
      | succ k ih =>
        intro hk
        have e : n - k = (n - (k+1)) + 1 := by omega
        have IH := ih (by omega)
        rw [e] at IH
        set i := n - (k+1) with hi
        have hin : i < n := by omega
        rw [sum_Ioc_step (fun l => greedy n p p' l true + greedy n p p' l false) n i hin,
          sum_Ioc_step (fun l => v l true + v l false) n i hin]
        beta_reduce
        set G := ∑ l ∈ Finset.Ioc (i+1) n, (greedy n p p' l true + greedy n p p' l false) with hG
        set V := ∑ l ∈ Finset.Ioc (i+1) n, (v l true + v l false) with hV
        have hD : 0 ≤ V - G := by linarith
        have hv' := hv (i+1) (by omega) (by omega)
        have hκT : 0 ≤ chat (i+1) p' true := by unfold chat; simp only [if_true]; apply div_nonneg <;> first | positivity | linarith
        have hκF : 0 ≤ chat (i+1) p' false := by unfold chat; simp only [Bool.false_eq_true, if_false]; apply div_nonneg <;> first | positivity | linarith
        have hcsum : chat (i+1) p' true + chat (i+1) p' false ≤ 1 := by
          unfold chat
          simp only [if_true, Bool.false_eq_true, if_false]
          have h1 : (1 : ℝ) ≤ ((i+1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ i+1)
          rw [← add_div]
          rw [div_le_one (by linarith)]
          linarith
        have hg : ∀ s, greedy n p p' (i+1) s ≤ v (i+1) s + chat (i+1) p' s * (V - G) := by
          intro s
          have hc0 : 0 ≤ chat (i+1) p' s := by cases s <;> assumption
          rw [greedy_rec n p p' (i+1) (by omega) (by omega) s]
          apply max_le
          · have := (hv' s).1; nlinarith [mul_nonneg hc0 hD]
          · have := (hv' s).2; nlinarith
        have h1 := hg true
        have h2 := hg false
        have h3 : (chat (i+1) p' true + chat (i+1) p' false) * (V - G) ≤ V - G :=
          mul_le_of_le_one_left hD hcsum
        nlinarith
    have h0 := key n le_rfl
    rw [Nat.sub_self] at h0
    have hI : Finset.Icc 1 n = Finset.Ioc 0 n := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
    unfold dualValue
    rw [hI]
    exact h0
