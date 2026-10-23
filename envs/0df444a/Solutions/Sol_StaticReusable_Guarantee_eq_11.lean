-- Prove2me | solution 1 for StaticReusable.Guarantee.eq_11
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T07:42:40.334213+00:00
-- url     : https://prove2.me/submissions/db11eb05-8de4-4e0f-ad03-d4fb3079d157

import Mathlib
import Definitions.Def_StaticReusable_Guarantee_Setting

open Finset

namespace SolSRGEq11
open StaticReusable.Guarantee

lemma weight_nonneg {C : ℕ} {μ Λ : ℝ} (hμ : 0 < μ) {lam : ℕ → ℝ} (hlam : lam ∈ Policies C Λ)
    (i : ℕ) : 0 ≤ weight C μ lam i := by
  unfold weight
  apply mul_nonneg (by positivity)
  apply Finset.prod_nonneg
  intro j hj
  simp only [Finset.mem_Icc] at hj
  have := (hlam j (by simp only [Finset.mem_Icc]; omega)).1
  positivity

lemma prob_nonneg {C : ℕ} {μ Λ : ℝ} (hμ : 0 < μ) {lam : ℕ → ℝ} (hlam : lam ∈ Policies C Λ)
    (i : ℕ) : 0 ≤ prob C μ lam i := by
  unfold prob
  exact div_nonneg (weight_nonneg hμ hlam i)
    (Finset.sum_nonneg (fun k _ => weight_nonneg hμ hlam k))

lemma ms_const (C : ℕ) (μ l : ℝ) :
    marketShare C μ (fun _ => l) = l * serviceLevel C μ (fun _ => l) := by
  unfold marketShare serviceLevel
  rw [Finset.mul_sum]

end SolSRGEq11

open SolSRGEq11 in
theorem solution {C : ℕ} {μ Λ : ℝ} (hμ : 0 < μ) (lam : ℕ → ℝ)
    (hlam : lam ∈ StaticReusable.Guarantee.Policies C Λ) :
    StaticReusable.Guarantee.marketShare C μ
        (fun _ => StaticReusable.Guarantee.staticRate C μ lam) *
        StaticReusable.Guarantee.serviceLevel C μ lam =
      StaticReusable.Guarantee.marketShare C μ lam *
        StaticReusable.Guarantee.serviceLevel C μ
          (fun _ => StaticReusable.Guarantee.staticRate C μ lam) := by
  open StaticReusable.Guarantee in
  rw [ms_const]
  by_cases h : serviceLevel C μ lam = 0
  · -- all probabilities vanish, so the market share vanishes too
    have hz : ∀ i ∈ Finset.Icc 1 C, prob C μ lam i = 0 := by
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => prob_nonneg hμ hlam i)).1 h
      exact this
    have hms : marketShare C μ lam = 0 := by
      unfold marketShare
      exact Finset.sum_eq_zero (fun i hi => by rw [hz i hi, mul_zero])
    rw [h, hms]; ring
  · have hst : staticRate C μ lam * serviceLevel C μ lam = marketShare C μ lam := by
      unfold staticRate
      change marketShare C μ lam / serviceLevel C μ lam * serviceLevel C μ lam = _
      field_simp
    rw [← hst]; ring
