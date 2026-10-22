-- Prove2me | solution 1 for ProductFraming.Pricing.eq_15
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T06:34:22.055885+00:00
-- url     : https://prove2.me/submissions/ca74981c-ad2f-4180-96e5-87abf6890e8b

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

lemma pf_revenue_not_mem {n : ℕ} (a : Fin n → ℝ) (β : ℝ) (r : Fin n → ℝ) (S : Finset (Fin n))
    (i : Fin n) (hi : i ∉ S) (t : ℝ) :
    revenue a β (Function.update r i t) S = revenue a β r S := by
  rw [pf_revenue_eq, pf_revenue_eq]
  have : ∀ k ∈ S, Function.update r i t k = r k := by
    intro k hk
    exact Function.update_of_ne (fun h => hi (by rw [← h]; exact hk)) _ _
  have e1 : ∑ k ∈ S, Function.update r i t k * Real.exp (a k - β * Function.update r i t k)
      = ∑ k ∈ S, r k * Real.exp (a k - β * r k) :=
    Finset.sum_congr rfl (fun k hk => by rw [this k hk])
  have e2 : ∑ k ∈ S, Real.exp (a k - β * Function.update r i t k)
      = ∑ k ∈ S, Real.exp (a k - β * r k) :=
    Finset.sum_congr rfl (fun k hk => by rw [this k hk])
  rw [e1, e2]

lemma pf_revenue_deriv {n : ℕ} (a : Fin n → ℝ) (β : ℝ) (hβ : β ≠ 0) (r : Fin n → ℝ)
    (S : Finset (Fin n)) (i : Fin n) (hi : i ∈ S) :
    HasDerivAt (fun t => revenue a β (Function.update r i t) S)
      (β * mnl a β r S i * (1 / β + revenue a β r S - r i)) (r i) := by
  have hterm : ∀ k ∈ S, HasDerivAt
      (fun t : ℝ => Function.update r i t k * Real.exp (a k - β * Function.update r i t k))
      (if k = i then Real.exp (a i - β * r i) * (1 - β * r i) else 0) (r i) := by
    intro k hk
    by_cases hki : k = i
    · subst hki
      have h1 : HasDerivAt (fun t : ℝ => t * Real.exp (a k - β * t))
          (1 * Real.exp (a k - β * r k) + r k * (Real.exp (a k - β * r k) * (0 - β * 1))) (r k) := by
        have hexp : HasDerivAt (fun t : ℝ => Real.exp (a k - β * t))
            (Real.exp (a k - β * r k) * (0 - β * 1)) (r k) := by
          apply HasDerivAt.exp
          exact (hasDerivAt_const _ _).sub ((hasDerivAt_id _).const_mul β)
        exact (hasDerivAt_id (r k)).mul hexp
      have e : (fun t : ℝ => Function.update r k t k * Real.exp (a k - β * Function.update r k t k))
          = fun t : ℝ => t * Real.exp (a k - β * t) := by
        funext t; simp
      rw [e, if_pos rfl]
      convert h1 using 1; ring
    · have e : (fun t : ℝ => Function.update r i t k * Real.exp (a k - β * Function.update r i t k))
          = fun _ => r k * Real.exp (a k - β * r k) := by
        funext t; rw [Function.update_of_ne hki]
      rw [e, if_neg hki]
      exact hasDerivAt_const _ _
  have hterm2 : ∀ k ∈ S, HasDerivAt
      (fun t : ℝ => Real.exp (a k - β * Function.update r i t k))
      (if k = i then Real.exp (a i - β * r i) * (-β) else 0) (r i) := by
    intro k hk
    by_cases hki : k = i
    · subst hki
      have e : (fun t : ℝ => Real.exp (a k - β * Function.update r k t k))
          = fun t : ℝ => Real.exp (a k - β * t) := by
        funext t; simp
      rw [e, if_pos rfl]
      have hexp : HasDerivAt (fun t : ℝ => Real.exp (a k - β * t))
            (Real.exp (a k - β * r k) * (0 - β * 1)) (r k) := by
        apply HasDerivAt.exp
        exact (hasDerivAt_const _ _).sub ((hasDerivAt_id _).const_mul β)
      convert hexp using 1; ring
    · have e : (fun t : ℝ => Real.exp (a k - β * Function.update r i t k))
          = fun _ => Real.exp (a k - β * r k) := by
        funext t; rw [Function.update_of_ne hki]
      rw [e, if_neg hki]
      exact hasDerivAt_const _ _
  have hN := HasDerivAt.fun_sum hterm
  have hZ := (HasDerivAt.fun_sum hterm2).const_add (1 : ℝ)
  rw [Finset.sum_ite_eq' S i, if_pos hi] at hN
  rw [Finset.sum_ite_eq' S i, if_pos hi] at hZ
  have hpos : 0 < 1 + ∑ k ∈ S, Real.exp (a k - β * r k) := by
    have : 0 ≤ ∑ k ∈ S, Real.exp (a k - β * r k) := Finset.sum_nonneg (fun k _ => (Real.exp_pos _).le)
    linarith
  have hdiv := hN.div hZ (by simpa using hpos.ne')
  have hfun2 : (fun t => revenue a β (Function.update r i t) S) = fun t =>
      (∑ k ∈ S, Function.update r i t k * Real.exp (a k - β * Function.update r i t k)) /
        (1 + ∑ k ∈ S, Real.exp (a k - β * Function.update r i t k)) := by
    funext t
    exact pf_revenue_eq a β _ S
  rw [hfun2]
  refine HasDerivAt.congr_deriv hdiv ?_
  simp only [Function.update_eq_self]
  rw [pf_revenue_eq]
  unfold mnl
  rw [if_pos hi]
  have hZ0 : (1 + ∑ k ∈ S, Real.exp (a k - β * r k)) ≠ 0 := hpos.ne'
  field_simp
  ring

theorem solution {n m p : ℕ} (a : Fin n → ℝ) (β : ℝ) (lam : ℕ → ℝ)
    (hβ : 0 < β) (hm : 1 ≤ m) (hp : 1 ≤ p) (hlam : ProductFraming.Nest.IsPageLaw m lam)
    (f : Fin n → ℕ) (hf : ProductFraming.Trunc.Feasible m p f) (r : Fin n → ℝ) (i : Fin n) (hi : 1 ≤ f i) :
    HasDerivAt (fun t : ℝ => totalRevenue m a β lam f (Function.update r i t))
      (β * ∑ l ∈ Icc (f i) m, lam l * mnl a β r (ProductFraming.Nest.consideration f l) i *
        (1 / β + revenue a β r (ProductFraming.Nest.consideration f l) - r i)) (r i) := by
  unfold totalRevenue
  have hmem : ∀ x, i ∈ ProductFraming.Nest.consideration f x ↔ f i ≤ x := by
    intro x
    simp only [ProductFraming.Nest.consideration, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨hi, h⟩
  have hterm : ∀ x ∈ Icc 1 m, HasDerivAt
      (fun t : ℝ => lam x * revenue a β (Function.update r i t) (ProductFraming.Nest.consideration f x))
      (if f i ≤ x then lam x * (β * mnl a β r (ProductFraming.Nest.consideration f x) i *
        (1 / β + revenue a β r (ProductFraming.Nest.consideration f x) - r i)) else 0) (r i) := by
    intro x _
    by_cases hx : f i ≤ x
    · rw [if_pos hx]
      exact (pf_revenue_deriv a β hβ.ne' r _ i ((hmem x).2 hx)).const_mul (lam x)
    · rw [if_neg hx]
      have e : (fun t : ℝ => lam x * revenue a β (Function.update r i t)
          (ProductFraming.Nest.consideration f x)) =
          fun _ => lam x * revenue a β r (ProductFraming.Nest.consideration f x) := by
        funext t
        rw [pf_revenue_not_mem a β r _ i (fun h => hx ((hmem x).1 h)) t]
      rw [e]
      exact hasDerivAt_const _ _
  refine HasDerivAt.congr_deriv (HasDerivAt.fun_sum hterm) ?_
  rw [← Finset.sum_filter, Finset.mul_sum]
  have hfil : (Icc 1 m).filter (fun x => f i ≤ x) = Icc (f i) m := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  rw [hfil]
  apply Finset.sum_congr rfl
  intro x _
  ring
