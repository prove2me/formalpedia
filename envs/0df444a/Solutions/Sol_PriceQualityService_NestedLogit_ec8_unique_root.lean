-- Prove2me | solution 1 for PriceQualityService.NestedLogit.ec8_unique_root
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T00:32:23.749835+00:00
-- url     : https://prove2.me/submissions/dba8680f-ae81-49a7-a236-49cdea607da5

import Mathlib
import Definitions.Def_PriceQualityService_NestedLogit_Optimum

set_option autoImplicit false

open PriceQualityService.NestedLogit

lemma pqn_sum_nest (f : Nest → ℝ) : ∑ x : Nest, f x = f Nest.s + f Nest.l := by
  have huniv : (Finset.univ : Finset Nest) = {Nest.s, Nest.l} := rfl
  rw [huniv, Finset.sum_pair (by decide)]

lemma pqn_fp_form (M : Model) (hμ : 1 ≤ M.μ₁) (q : Vec M) (r : ℝ) :
    fixedPointRHS M q r =
      Real.exp (-(r / M.μ₁) - 1) *
        ∑ x : Nest, M.μ₁ * (∑ j, Real.exp (netUtility M q x j)) ^ (1 / M.μ₁) := by
  have hμ0 : 0 < M.μ₁ := by linarith
  unfold fixedPointRHS
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  have h1 : ∑ j, Real.exp (netUtility M q x j - r - M.μ₁) =
      Real.exp (-r - M.μ₁) * ∑ j, Real.exp (netUtility M q x j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← Real.exp_add]; congr 1; ring
  rw [h1, Real.mul_rpow (Real.exp_pos _).le (Finset.sum_nonneg (fun j _ => (Real.exp_pos _).le)),
    ← Real.exp_mul]
  have h2 : (-r - M.μ₁) * (1 / M.μ₁) = -(r / M.μ₁) - 1 := by field_simp
  rw [h2]; ring

theorem solution (M : Model) (hμ : 1 ≤ M.μ₁) (hc : ∀ x i, 0 < M.c x i) (q : Vec M) :
    ((0 < M.m Nest.s ∨ 0 < M.m Nest.l) → StrictAnti (fun r : ℝ => fixedPointRHS M q r)) ∧
      ∃! r : ℝ, r = fixedPointRHS M q r := by
  have hμ0 : 0 < M.μ₁ := by linarith
  set K : ℝ := ∑ x : Nest, M.μ₁ * (∑ j, Real.exp (netUtility M q x j)) ^ (1 / M.μ₁) with hK
  have hK0 : 0 ≤ K := Finset.sum_nonneg (fun x _ =>
    mul_nonneg hμ0.le (Real.rpow_nonneg (Finset.sum_nonneg (fun j _ => (Real.exp_pos _).le)) _))
  have hform := pqn_fp_form M hμ q
  have hanti : Antitone (fun r : ℝ => fixedPointRHS M q r) := by
    intro r1 r2 h
    simp only [hform]
    apply mul_le_mul_of_nonneg_right _ hK0
    apply Real.exp_le_exp.mpr
    have : r1 / M.μ₁ ≤ r2 / M.μ₁ := div_le_div_of_nonneg_right h hμ0.le
    linarith
  refine ⟨?_, ?_⟩
  · intro hne
    have hKpos : 0 < K := by
      rw [hK, pqn_sum_nest]
      have hs : 0 ≤ M.μ₁ * (∑ j, Real.exp (netUtility M q Nest.s j)) ^ (1 / M.μ₁) :=
        mul_nonneg hμ0.le (Real.rpow_nonneg (Finset.sum_nonneg (fun j _ => (Real.exp_pos _).le)) _)
      have hl : 0 ≤ M.μ₁ * (∑ j, Real.exp (netUtility M q Nest.l j)) ^ (1 / M.μ₁) :=
        mul_nonneg hμ0.le (Real.rpow_nonneg (Finset.sum_nonneg (fun j _ => (Real.exp_pos _).le)) _)
      rcases hne with h | h
      · have : 0 < ∑ j, Real.exp (netUtility M q Nest.s j) :=
          Finset.sum_pos (fun j _ => Real.exp_pos _) (Finset.univ_nonempty_iff.mpr ⟨⟨0, h⟩⟩)
        have := Real.rpow_pos_of_pos this (1 / M.μ₁)
        have := mul_pos hμ0 this
        linarith
      · have : 0 < ∑ j, Real.exp (netUtility M q Nest.l j) :=
          Finset.sum_pos (fun j _ => Real.exp_pos _) (Finset.univ_nonempty_iff.mpr ⟨⟨0, h⟩⟩)
        have := Real.rpow_pos_of_pos this (1 / M.μ₁)
        have := mul_pos hμ0 this
        linarith
    intro r1 r2 h
    simp only [hform]
    apply mul_lt_mul_of_pos_right _ hKpos
    apply Real.exp_lt_exp.mpr
    have : r1 / M.μ₁ < r2 / M.μ₁ := div_lt_div_of_pos_right h hμ0
    linarith
  · have hcont : Continuous (fun r : ℝ => r - fixedPointRHS M q r) := by
      have : ∀ r : ℝ, fixedPointRHS M q r = Real.exp (-(r / M.μ₁) - 1) * K := fun r => by
        rw [hform]
      simp only [this]
      fun_prop
    have hF0 : 0 ≤ fixedPointRHS M q 0 := by
      rw [hform]; exact mul_nonneg (Real.exp_pos _).le hK0
    have h0 : (fun r : ℝ => r - fixedPointRHS M q r) 0 ≤ 0 := by
      simp only; linarith
    have h1 : 0 ≤ (fun r : ℝ => r - fixedPointRHS M q r) (fixedPointRHS M q 0) := by
      simp only
      have := hanti hF0
      linarith
    obtain ⟨r, -, hr⟩ := intermediate_value_Icc hF0 hcont.continuousOn ⟨h0, h1⟩
    refine ⟨r, by simp only at hr; linarith, ?_⟩
    intro r' hr'
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have := hanti h.le
      simp only at hr
      linarith
    · have := hanti h.le
      simp only at hr
      linarith
