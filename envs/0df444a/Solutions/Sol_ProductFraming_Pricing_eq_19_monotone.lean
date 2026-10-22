-- Prove2me | solution 1 for ProductFraming.Pricing.eq_19_monotone
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T06:42:24.567986+00:00
-- url     : https://prove2.me/submissions/fb010cdb-3b99-427e-a737-5f8792cc098d

import Mathlib
import Definitions.Def_ProductFraming_Pricing_MNL
import Definitions.Def_ProductFraming_Pricing_Model

set_option autoImplicit false
open Finset ProductFraming.Pricing

lemma pf_revenue_eq {n : ℕ} (a : Fin n → ℝ) (β : ℝ) (r : Fin n → ℝ) (S : Finset (Fin n)) :
    revenue a β r S = (∑ k ∈ S, r k * Real.exp (a k - β * r k)) /
      (1 + ∑ k ∈ S, Real.exp (a k - β * r k)) := by
  unfold revenue mnl
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  rw [if_pos hk, mul_div_assoc]


lemma pf_mnl_nonneg {n : ℕ} (a : Fin n → ℝ) (β : ℝ) (r : Fin n → ℝ) (S : Finset (Fin n))
    (k : Fin n) : 0 ≤ mnl a β r S k := by
  unfold mnl
  split_ifs
  · apply div_nonneg (Real.exp_pos _).le
    have : 0 ≤ ∑ k' ∈ S, Real.exp (a k' - β * r k') := Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le)
    linarith
  · exact le_rfl

lemma pf_mnl_shift {n : ℕ} (a : Fin n → ℝ) (β : ℝ) (hβ : β ≠ 0) (r : Fin n → ℝ)
    (S : Finset (Fin n)) (i : Fin n) (t : ℝ) (k : Fin n) :
    mnl (Function.update a i t) β (Function.update r i (r i + (t - a i) / β)) S k
      = mnl a β r S k := by
  have heq : ∀ k', Function.update a i t k' - β * Function.update r i (r i + (t - a i) / β) k'
      = a k' - β * r k' := by
    intro k'
    by_cases h : k' = i
    · subst h
      simp only [Function.update_self]
      field_simp
      ring
    · rw [Function.update_of_ne h, Function.update_of_ne h]
  unfold mnl
  simp only [heq]

lemma pf_rev_shift {n : ℕ} (a : Fin n → ℝ) (β : ℝ) (hβ : β ≠ 0) (r : Fin n → ℝ)
    (S : Finset (Fin n)) (i : Fin n) (t : ℝ) :
    revenue (Function.update a i t) β (Function.update r i (r i + (t - a i) / β)) S
      = revenue a β r S + (t - a i) / β * mnl a β r S i := by
  unfold revenue
  have h1 : ∀ k ∈ S, Function.update r i (r i + (t - a i) / β) k *
        mnl (Function.update a i t) β (Function.update r i (r i + (t - a i) / β)) S k
      = r k * mnl a β r S k + (if k = i then (t - a i) / β * mnl a β r S k else 0) := by
    intro k hk
    rw [pf_mnl_shift a β hβ r S i t k]
    by_cases h : k = i
    · subst h
      simp only [Function.update_self, if_true]
      ring
    · rw [Function.update_of_ne h, if_neg h]
      ring
  rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_ite_eq' S i]
  by_cases hi : i ∈ S
  · rw [if_pos hi]
  · rw [if_neg hi]
    have : mnl a β r S i = 0 := by unfold mnl; rw [if_neg hi]
    rw [this]; simp

lemma pf_term_le {n : ℕ} (a : Fin n → ℝ) (β : ℝ) (hβ : 0 < β) (x : ℝ) (k : Fin n) :
    x * Real.exp (a k - β * x) ≤ Real.exp (a k) / β := by
  rw [le_div_iff₀ hβ]
  have h := Real.add_one_le_exp (β * x)
  have h2 : β * x * Real.exp (-(β * x)) ≤ Real.exp (β * x) * Real.exp (-(β * x)) :=
    mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at h2
  have e : Real.exp (a k - β * x) = Real.exp (a k) * Real.exp (-(β * x)) := by
    rw [← Real.exp_add]; ring_nf
  rw [e]
  have := mul_le_mul_of_nonneg_left h2 (Real.exp_pos (a k)).le
  nlinarith

lemma pf_rev_le {n : ℕ} (a : Fin n → ℝ) (β : ℝ) (hβ : 0 < β) (r : Fin n → ℝ)
    (S : Finset (Fin n)) : revenue a β r S ≤ ∑ k : Fin n, Real.exp (a k) / β := by
  rw [pf_revenue_eq]
  have hB : 0 ≤ ∑ k : Fin n, Real.exp (a k) / β :=
    Finset.sum_nonneg (fun k _ => div_nonneg (Real.exp_pos _).le hβ.le)
  have hZ : 1 ≤ 1 + ∑ k ∈ S, Real.exp (a k - β * r k) := by
    have : 0 ≤ ∑ k ∈ S, Real.exp (a k - β * r k) := Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le)
    linarith
  rw [div_le_iff₀ (by linarith)]
  have hN : ∑ k ∈ S, r k * Real.exp (a k - β * r k) ≤ ∑ k : Fin n, Real.exp (a k) / β := by
    calc ∑ k ∈ S, r k * Real.exp (a k - β * r k) ≤ ∑ k ∈ S, Real.exp (a k) / β :=
          Finset.sum_le_sum (fun k _ => pf_term_le a β hβ (r k) k)
      _ ≤ ∑ k : Fin n, Real.exp (a k) / β :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun k _ _ => div_nonneg (Real.exp_pos _).le hβ.le)
  nlinarith

theorem solution {n m p : ℕ} (a : Fin n → ℝ) (β : ℝ) (lam : ℕ → ℝ)
    (hβ : 0 < β) (hm : 1 ≤ m) (hp : 1 ≤ p) (hlam : ProductFraming.Nest.IsPageLaw m lam)
    (f : Fin n → ℕ) (hf : ProductFraming.Trunc.Feasible m p f) (i : Fin n) (hi : 1 ≤ f i) (t : ℝ) (ht : a i ≤ t) :
    BddAbove (Set.range (totalRevenue m a β lam f)) ∧
      BddAbove (Set.range (totalRevenue m (Function.update a i t) β lam f)) ∧
      optRevenue m a β lam f ≤ optRevenue m (Function.update a i t) β lam f := by
  have hlam0 : ∀ x ∈ Icc 1 m, 0 ≤ lam x := hlam.1
  have hbdd : ∀ a' : Fin n → ℝ, BddAbove (Set.range (totalRevenue m a' β lam f)) := by
    intro a'
    refine ⟨∑ x ∈ Icc 1 m, lam x * ∑ k : Fin n, Real.exp (a' k) / β, ?_⟩
    rintro y ⟨r', rfl⟩
    unfold totalRevenue
    exact Finset.sum_le_sum (fun x hx => mul_le_mul_of_nonneg_left (pf_rev_le a' β hβ r' _) (hlam0 x hx))
  refine ⟨hbdd a, hbdd _, ?_⟩
  unfold optRevenue
  refine ciSup_le (fun r => ?_)
  refine le_trans ?_ (le_ciSup (hbdd (Function.update a i t)) (Function.update r i (r i + (t - a i) / β)))
  unfold totalRevenue
  apply Finset.sum_le_sum
  intro x hx
  apply mul_le_mul_of_nonneg_left _ (hlam0 x hx)
  rw [pf_rev_shift a β hβ.ne' r _ i t]
  have : 0 ≤ (t - a i) / β * mnl a β r (ProductFraming.Nest.consideration f x) i :=
    mul_nonneg (div_nonneg (by linarith) hβ.le) (pf_mnl_nonneg _ _ _ _ _)
  linarith
