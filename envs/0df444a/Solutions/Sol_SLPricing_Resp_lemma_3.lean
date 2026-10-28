-- Prove2me | solution 1 for SLPricing.Resp.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T18:18:20.08674+00:00
-- url     : https://prove2.me/submissions/53745fac-403e-424d-8128-7f7cf22d8b0f

import Mathlib
import Definitions.Def_SLPricing_Resp_Model
import Definitions.Def_SLPricing_Resp_P2Star
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace Aux_SLPR_L3

open SLPricing.Resp

lemma late_eq (xbar : ℝ) (hx : xbar ∈ Icc (0 : ℝ) 1) (p q : ℝ) :
    lateMass (Icc xbar 1) p q = max (xbar - max 0 (p - q)) 0 := by
  unfold lateMass
  have hset : {x ∈ Icc (0 : ℝ) 1 \ Icc xbar 1 | p ≤ x + q} = Ico (max 0 (p - q)) xbar := by
    ext x
    simp only [mem_setOf_eq, mem_diff, mem_Icc, mem_Ico, max_le_iff, not_and, not_le]
    constructor
    · rintro ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩
      refine ⟨⟨h0, by linarith⟩, ?_⟩
      by_contra h
      push_neg at h
      exact absurd (h2 h) (not_lt.mpr h1)
    · rintro ⟨⟨h0, h3⟩, h4⟩
      exact ⟨⟨⟨h0, by linarith [hx.2]⟩, fun h => absurd h (not_le.mpr h4)⟩, by linarith⟩
  rw [hset, Real.volume_Ico, ENNReal.toReal_ofReal']

end Aux_SLPR_L3

open SLPricing.Resp in
theorem solution (P : Params) (hP : P.Standing) (B : Set ℝ) (xbar : ℝ)
    (hx : xbar ∈ Icc (0 : ℝ) 1) (hB : B = Icc xbar 1) (q : ℝ) :
    (∀ p₂, secondProfit P B q p₂ ≤ secondProfit P B q (SLPricing.Resp.p2Star P.c q xbar)) ∧
    (0 < xbar → P.c - xbar < q → ∀ p₂, (∀ p, secondProfit P B q p ≤ secondProfit P B q p₂) →
      p₂ = SLPricing.Resp.p2Star P.c q xbar) ∧
    (q ≤ P.c - xbar → ∀ p₂, (∀ p, secondProfit P B q p ≤ secondProfit P B q p₂) →
      lateMass B p₂ q = 0) := by
  subst hB
  obtain ⟨hx0, hx1⟩ := hx
  set c := P.c with hcdef
  have hm := Aux_SLPR_L3.late_eq xbar ⟨hx0, hx1⟩
  have mA : ∀ p, p ≤ q → lateMass (Icc xbar 1) p q = xbar := by
    intro p hp
    rw [hm, max_eq_left (by linarith : (0:ℝ) ≥ p - q), sub_zero, max_eq_left hx0]
  have mB : ∀ p, q ≤ p → p ≤ q + xbar → lateMass (Icc xbar 1) p q = xbar + q - p := by
    intro p hp1 hp2
    rw [hm, max_eq_right (by linarith : (0:ℝ) ≤ p - q), max_eq_left (by linarith)]
    ring
  have mC : ∀ p, q + xbar ≤ p → lateMass (Icc xbar 1) p q = 0 := by
    intro p hp
    rw [hm, max_eq_right (by linarith : (0:ℝ) ≤ p - q), max_eq_right (by linarith)]
  have hSP : ∀ p, secondProfit P (Icc xbar 1) q p = (p - c) * lateMass (Icc xbar 1) p q :=
    fun p => rfl
  -- profit in each region
  have πA : ∀ p, p ≤ q → secondProfit P (Icc xbar 1) q p = (p - c) * xbar := by
    intro p hp; rw [hSP, mA p hp]
  have πB : ∀ p, q ≤ p → p ≤ q + xbar →
      secondProfit P (Icc xbar 1) q p = (p - c) * (xbar + q - p) := by
    intro p h1 h2; rw [hSP, mB p h1 h2]
  have πC : ∀ p, q + xbar ≤ p → secondProfit P (Icc xbar 1) q p = 0 := by
    intro p hp; rw [hSP, mC p hp, mul_zero]
  -- trichotomy helper
  have tri : ∀ p : ℝ, p ≤ q ∨ (q ≤ p ∧ p ≤ q + xbar) ∨ q + xbar ≤ p := by
    intro p
    rcases le_total p q with h | h
    · exact Or.inl h
    · rcases le_total p (q + xbar) with h' | h'
      · exact Or.inr (Or.inl ⟨h, h'⟩)
      · exact Or.inr (Or.inr h')
  -- the optimal value
  have hopt : ∀ p, secondProfit P (Icc xbar 1) q p ≤
      secondProfit P (Icc xbar 1) q (SLPricing.Resp.p2Star c q xbar) := by
    intro p
    unfold SLPricing.Resp.p2Star
    by_cases h1 : q ≤ c - xbar
    · rw [if_pos h1, πC c (by linarith)]
      rcases tri p with h | ⟨h, h'⟩ | h
      · rw [πA p h]; nlinarith
      · rw [πB p h h']; nlinarith
      · rw [πC p h]
    · rw [if_neg h1]
      by_cases h2 : q ≤ c + xbar
      · rw [if_pos h2, πB ((q + c + xbar) / 2) (by linarith) (by linarith)]
        rcases tri p with h | ⟨h, h'⟩ | h
        · rw [πA p h]; nlinarith [sq_nonneg (q - (q + c + xbar) / 2)]
        · rw [πB p h h']; nlinarith [sq_nonneg (p - (q + c + xbar) / 2)]
        · rw [πC p h]; nlinarith
      · rw [if_neg h2, πA q le_rfl]
        rcases tri p with h | ⟨h, h'⟩ | h
        · rw [πA p h]; nlinarith
        · rw [πB p h h']; nlinarith
        · rw [πC p h]; nlinarith
  refine ⟨hopt, ?_, ?_⟩
  · intro hxpos hq p₂ hp₂
    have heq : secondProfit P (Icc xbar 1) q p₂ =
        secondProfit P (Icc xbar 1) q (SLPricing.Resp.p2Star c q xbar) :=
      le_antisymm (hopt p₂) (hp₂ _)
    unfold SLPricing.Resp.p2Star at heq ⊢
    have h1 : ¬ q ≤ c - xbar := by linarith
    rw [if_neg h1] at heq ⊢
    by_cases h2 : q ≤ c + xbar
    · rw [if_pos h2] at heq ⊢
      rw [πB ((q + c + xbar) / 2) (by linarith) (by linarith)] at heq
      rcases tri p₂ with h | ⟨h, h'⟩ | h
      · rw [πA p₂ h] at heq
        have e1 : (q - c) * xbar = ((q + c + xbar) / 2 - c) * (xbar + q - (q + c + xbar) / 2)
            - (q - (q + c + xbar) / 2) ^ 2 := by ring
        have h3 : (q - p₂) * xbar + (q - (q + c + xbar) / 2) ^ 2 = 0 := by
          linear_combination e1 - heq
        have h4 : 0 ≤ (q - p₂) * xbar := mul_nonneg (by linarith) hx0
        have h5 : (q - (q + c + xbar) / 2) ^ 2 = 0 := by
          nlinarith [sq_nonneg (q - (q + c + xbar) / 2)]
        have h6 : (q - p₂) * xbar = 0 := by linarith
        have hq' : q - (q + c + xbar) / 2 = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp h5
        rcases mul_eq_zero.mp h6 with h7 | h7
        · linarith
        · linarith
      · rw [πB p₂ h h'] at heq
        nlinarith [sq_nonneg (p₂ - (q + c + xbar) / 2)]
      · rw [πC p₂ h] at heq
        nlinarith
    · rw [if_neg h2] at heq ⊢
      rw [πA q le_rfl] at heq
      rcases tri p₂ with h | ⟨h, h'⟩ | h
      · rw [πA p₂ h] at heq
        nlinarith
      · rw [πB p₂ h h'] at heq
        nlinarith
      · rw [πC p₂ h] at heq
        nlinarith
  · intro hq p₂ hp₂
    have h0 : secondProfit P (Icc xbar 1) q c = 0 := πC c (by linarith)
    have hge := hp₂ c
    rw [h0] at hge
    have hle := hopt p₂
    unfold SLPricing.Resp.p2Star at hle
    rw [if_pos hq, h0] at hle
    have hz : (p₂ - c) * lateMass (Icc xbar 1) p₂ q = 0 := by
      rw [← hSP]; linarith
    rcases mul_eq_zero.mp hz with h | h
    · have : p₂ = c := by linarith
      rw [this]; exact mC c (by linarith)
    · exact h
