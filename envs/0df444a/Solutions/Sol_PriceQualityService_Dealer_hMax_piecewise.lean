-- Prove2me | solution 1 for PriceQualityService.Dealer.hMax_piecewise
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:45:08.092935+00:00
-- url     : https://prove2.me/submissions/c988b220-7bda-47af-a5b3-db10171430d8

import Mathlib
import Definitions.Def_PriceQualityService_Dealer_Model
import Definitions.Def_PriceQualityService_Dealer_Breakpoints

set_option autoImplicit false
open Finset PriceQualityService.Dealer

theorem solution {N : ℕ} (α a b c s p q : Fin N → ℝ) (ts tl : ℝ) (hts : ts < tl)
    (i : Fin N) (hs : 0 < s i) (hg : 0 ≤ a i - b i * q i) :
    (∀ r : ℝ, r ≤ adjustedMarkup a b c s p q ts tl i →
      hMax α a b c s p q ts tl i r = hLong α a b c s p q tl i r) ∧
    (∀ r : ℝ, adjustedMarkup a b c s p q ts tl i < r → r ≤ markup a b c p q ts i →
      hMax α a b c s p q ts tl i r = hShort α a b c s p q ts i r) ∧
    (∀ r : ℝ, markup a b c p q ts i < r → hMax α a b c s p q ts tl i r = 0) := by
  set g := a i - b i * q i with hgdef
  set base := p i - c i * q i ^ 2 with hbase
  set El := Real.exp (tl * s i) with hEl
  set Es := Real.exp (ts * s i) with hEs
  have hEs0 : 0 < Es := Real.exp_pos _
  have hlt : Es < El := Real.exp_lt_exp.mpr (by nlinarith)
  have hd : 0 < El - Es := by linarith
  set K := Real.exp (α i * q i - p i) with hK
  have hK0 : 0 < K := Real.exp_pos _
  have hatl : attraction α s p q tl i = K * El := by
    unfold attraction; rw [hK, hEl, ← Real.exp_add]
  have hats : attraction α s p q ts i = K * Es := by
    unfold attraction; rw [hK, hEs, ← Real.exp_add]
  have hml : markup a b c p q tl i = base - tl * g := by unfold markup; ring
  have hms : markup a b c p q ts i = base - ts * g := by unfold markup; ring
  set A := (tl * El - ts * Es) / (El - Es) with hA
  have hAdj : adjustedMarkup a b c s p q ts tl i = base - A * g := by
    unfold adjustedMarkup adjFactor; rfl
  have hAtl : tl ≤ A := by
    rw [hA, le_div_iff₀ hd]
    nlinarith [mul_pos hEs0 (sub_pos.mpr hts)]
  have hLong : hLong α a b c s p q tl i = fun r => (base - tl * g - r) * (K * El) := by
    funext r; unfold PriceQualityService.Dealer.hLong; rw [hml, hatl]
  have hShort : hShort α a b c s p q ts i = fun r => (base - ts * g - r) * (K * Es) := by
    funext r; unfold PriceQualityService.Dealer.hShort; rw [hms, hats]
  -- difference identity
  have hdiff : ∀ r, (base - tl * g - r) * (K * El) - (base - ts * g - r) * (K * Es) =
      K * (El - Es) * ((base - A * g) - r) := by
    intro r
    have : A * (El - Es) = tl * El - ts * Es := by rw [hA]; field_simp
    linear_combination (K * g) * this
  have hKd : 0 < K * (El - Es) := mul_pos hK0 hd
  refine ⟨?_, ?_, ?_⟩
  · intro r hr
    rw [hAdj] at hr
    have h1 : 0 ≤ (base - tl * g - r) * (K * El) := by
      apply mul_nonneg _ (mul_pos hK0 (by linarith)).le
      nlinarith
    have h2 : (base - ts * g - r) * (K * Es) ≤ (base - tl * g - r) * (K * El) := by
      have := hdiff r
      nlinarith [mul_nonneg hKd.le (sub_nonneg.mpr hr)]
    unfold PriceQualityService.Dealer.hMax
    rw [hLong, hShort]
    simp only
    rw [max_eq_left h2, max_eq_left h1]
  · intro r hr1 hr2
    rw [hAdj] at hr1
    rw [hms] at hr2
    have h1 : 0 ≤ (base - ts * g - r) * (K * Es) := by
      apply mul_nonneg _ (mul_pos hK0 hEs0).le
      linarith
    have h2 : (base - tl * g - r) * (K * El) ≤ (base - ts * g - r) * (K * Es) := by
      have := hdiff r
      nlinarith [mul_pos hKd (sub_pos.mpr hr1)]
    unfold PriceQualityService.Dealer.hMax
    rw [hLong, hShort]
    simp only
    rw [max_eq_right h2, max_eq_left h1]
  · intro r hr
    rw [hms] at hr
    have h1 : (base - ts * g - r) * (K * Es) ≤ 0 := by
      apply mul_nonpos_of_nonpos_of_nonneg _ (mul_pos hK0 hEs0).le
      linarith
    have h2 : (base - tl * g - r) * (K * El) ≤ 0 := by
      apply mul_nonpos_of_nonpos_of_nonneg _ (mul_pos hK0 (by linarith)).le
      nlinarith
    unfold PriceQualityService.Dealer.hMax
    rw [hLong, hShort]
    simp only
    rw [max_eq_right (max_le h2 h1)]
