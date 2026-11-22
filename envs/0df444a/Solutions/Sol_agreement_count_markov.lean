-- Prove2me | solution 1 for agreement_count_markov
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:42:53.902963+00:00
-- url     : https://prove2.me/submissions/26df35ef-b330-4e05-a7c2-99df8c6441c2

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_Online
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_PAC
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Structures
public import Mathlib.Combinatorics.SetFamily.Shatter
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Theorems.Thm_disagreement_sum_eq

set_option autoImplicit true
@[expose] public section
public section
universe u v
theorem _root_.solution {α : Type*} [Fintype α] [DecidableEq α]
    (h : α → Bool) (hn : 1 ≤ Fintype.card α) :
    4 * (Finset.univ.filter fun f : α → Bool =>
      (Finset.univ.filter fun x => f x ≠ h x).card ≤ Fintype.card α / 4).card
    < 3 * 2 ^ Fintype.card α := by
  set n := Fintype.card α with hn_def
  set disagree_count : (α → Bool) → ℕ := fun f =>
    (Finset.univ.filter fun x => f x ≠ h x).card
  -- Step 1: Σ disagree = n · 2^(n-1)
  have hsum_disagree : ∑ f : α → Bool, disagree_count f = n * 2 ^ (n - 1) :=
    disagreement_sum_eq h
  have hdc_le_n : ∀ f : α → Bool, disagree_count f ≤ n := fun f => Finset.card_filter_le _ _
  -- Step 2: Σ agree = n · 2^(n-1)
  have hn1 : 1 ≤ n := hn
  have hpow : 2 * 2 ^ (n - 1) = 2 ^ n := by
    have hne : n ≠ 0 := by omega
    have ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hne
    rw [hk]; simp [pow_succ]; ring
  have hsum_agree : ∑ f : α → Bool, (n - disagree_count f) = n * 2 ^ (n - 1) := by
    have hcard_fun : Fintype.card (α → Bool) = 2 ^ n := by
      rw [Fintype.card_fun, Fintype.card_bool]
    have htotal : ∑ _f : α → Bool, n = 2 ^ n * n := by
      simp [Finset.sum_const, Finset.card_univ, hcard_fun]
    have hadd : ∑ f : α → Bool, (n - disagree_count f) +
        ∑ f : α → Bool, disagree_count f = ∑ _f : α → Bool, n := by
      rw [← Finset.sum_add_distrib]
      simp_all
    rw [htotal, hsum_disagree] at hadd
    nlinarith [hpow]
  -- Step 3: S = #{f : disagree ≤ n/4}
  set S := (Finset.univ.filter fun f : α → Bool =>
    disagree_count f ≤ n / 4).card with hS_def
  -- Step 4: Markov: S · (n - n/4) ≤ Σ agree = n · 2^(n-1)
  have hmarkov : S * (n - n / 4) ≤ n * 2 ^ (n - 1) := by
    calc S * (n - n / 4)
        ≤ ∑ f ∈ Finset.univ.filter (fun f : α → Bool => disagree_count f ≤ n / 4),
            (n - disagree_count f) := by
          rw [hS_def]
          apply Finset.card_nsmul_le_sum
          intro f hf
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
          omega
      _ ≤ ∑ f : α → Bool, (n - disagree_count f) :=
          Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
      _ = n * 2 ^ (n - 1) := hsum_agree
  -- Step 5: 3(n - n/4) > 2n for n ≥ 1
  have h3_gt : 2 * n < 3 * (n - n / 4) := by omega
  -- Step 6: Chain: 4S < 3 · 2^n
  have h_lhs : 4 * S * (n - n / 4) ≤ 2 * n * 2 ^ n := by
    calc 4 * S * (n - n / 4) = 4 * (S * (n - n / 4)) := by ring
      _ ≤ 4 * (n * 2 ^ (n - 1)) := by omega
      _ = 2 * n * (2 * 2 ^ (n - 1)) := by ring
      _ = 2 * n * 2 ^ n := by rw [hpow]
  have h_rhs : 2 * n * 2 ^ n < 3 * 2 ^ n * (n - n / 4) := by
    have hpow_pos : 0 < 2 ^ n := Nat.pos_of_ne_zero (by positivity)
    nlinarith
  have h_combined : 4 * S * (n - n / 4) < 3 * 2 ^ n * (n - n / 4) := by omega
  exact Nat.lt_of_mul_lt_mul_right h_combined
