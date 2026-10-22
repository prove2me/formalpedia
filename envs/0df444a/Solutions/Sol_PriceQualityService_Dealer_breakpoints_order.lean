-- Prove2me | solution 1 for PriceQualityService.Dealer.breakpoints_order
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:46:47.572154+00:00
-- url     : https://prove2.me/submissions/eb692682-a5af-4899-884a-0e5c5332bd86

import Mathlib
import Definitions.Def_PriceQualityService_Dealer_Model
import Definitions.Def_PriceQualityService_Dealer_Breakpoints

set_option autoImplicit false
open Finset PriceQualityService.Dealer

theorem solution {N : ℕ} (α a b c s p q : Fin N → ℝ) (ts tl : ℝ) (hts : ts < tl)
    (i : Fin N) (hs : 0 < s i) (hg : 0 ≤ a i - b i * q i) :
    (∀ r : ℝ, hLong α a b c s p q tl i r = hShort α a b c s p q ts i r ↔
      r = adjustedMarkup a b c s p q ts tl i) ∧
    (∀ r : ℝ, hLong α a b c s p q tl i r = 0 ↔ r = markup a b c p q tl i) ∧
    (∀ r : ℝ, hShort α a b c s p q ts i r = 0 ↔ r = markup a b c p q ts i) ∧
    adjustedMarkup a b c s p q ts tl i ≤ markup a b c p q tl i ∧
    markup a b c p q tl i ≤ markup a b c p q ts i := by
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
  have hdiff : ∀ r, (base - tl * g - r) * (K * El) - (base - ts * g - r) * (K * Es) =
      K * (El - Es) * ((base - A * g) - r) := by
    intro r
    have : A * (El - Es) = tl * El - ts * Es := by rw [hA]; field_simp
    linear_combination (K * g) * this
  have hKd : 0 < K * (El - Es) := mul_pos hK0 hd
  have hKl : 0 < K * El := mul_pos hK0 (by linarith)
  have hKs : 0 < K * Es := mul_pos hK0 hEs0
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro r
    rw [hLong, hShort, hAdj]
    simp only
    constructor
    · intro h
      have := hdiff r
      rw [h, sub_self] at this
      have h2 : (base - A * g) - r = 0 := by
        rcases mul_eq_zero.mp this.symm with h | h
        · exact absurd h hKd.ne'
        · exact h
      linarith
    · intro h
      have := hdiff r
      have h0 : (base - A * g) - r = 0 := by linarith
      rw [h0, mul_zero] at this
      linarith
  · intro r
    rw [hLong, hml]
    simp only
    constructor
    · intro h
      rcases mul_eq_zero.mp h with h | h
      · linarith
      · exact absurd h hKl.ne'
    · intro h; rw [h]; ring
  · intro r
    rw [hShort, hms]
    simp only
    constructor
    · intro h
      rcases mul_eq_zero.mp h with h | h
      · linarith
      · exact absurd h hKs.ne'
    · intro h; rw [h]; ring
  · rw [hAdj, hml]; nlinarith
  · rw [hml, hms]; nlinarith
