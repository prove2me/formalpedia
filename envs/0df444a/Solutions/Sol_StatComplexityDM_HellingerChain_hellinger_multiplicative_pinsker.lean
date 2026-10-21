-- Prove2me | solution 1 for StatComplexityDM.HellingerChain.hellinger_multiplicative_pinsker
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T02:01:09.288242+00:00
-- url     : https://prove2.me/submissions/559d62f3-1009-4e8a-bb61-f4ea23cace42

import Mathlib
import Definitions.Def_FoundationsRL_GeneralDM_Divergences

set_option autoImplicit false
open FoundationsRL.GeneralDM

theorem solution {Y : Type*} [Fintype Y] (P Q : Y → ℝ)
    (hP : (∀ y, 0 ≤ P y) ∧ ∑ y, P y = 1) (hQ : (∀ y, 0 ≤ Q y) ∧ ∑ y, Q y = 1)
    (h : Y → ℝ) (R : ℝ) (hh : ∀ y, (0 < P y ∨ 0 < Q y) → 0 ≤ h y ∧ h y ≤ R) :
    |∑ y, P y * h y - ∑ y, Q y * h y| ≤
        Real.sqrt (2 * R * (∑ y, P y * h y + ∑ y, Q y * h y) * hellingerSq P Q) ∧
      ∑ y, P y * h y ≤ 3 * ∑ y, Q y * h y + 4 * R * hellingerSq P Q := by
  obtain ⟨hP0, hP1⟩ := hP
  obtain ⟨hQ0, hQ1⟩ := hQ
  have hR : 0 ≤ R := by
    obtain ⟨y, hy⟩ : ∃ y, 0 < P y := by
      by_contra hne
      push_neg at hne
      have : ∑ y, P y ≤ 0 := Finset.sum_nonpos fun y _ => hne y
      linarith
    have := hh y (Or.inl hy)
    linarith [this.1, this.2]
  have hPh : ∀ y, 0 ≤ P y * h y := fun y => by
    by_cases hy : 0 < P y ∨ 0 < Q y
    · exact mul_nonneg (hP0 y) (hh y hy).1
    · push_neg at hy
      have : P y = 0 := le_antisymm hy.1 (hP0 y)
      simp [this]
  have hQh : ∀ y, 0 ≤ Q y * h y := fun y => by
    by_cases hy : 0 < P y ∨ 0 < Q y
    · exact mul_nonneg (hQ0 y) (hh y hy).1
    · push_neg at hy
      have : Q y = 0 := le_antisymm hy.2 (hQ0 y)
      simp [this]
  set a := ∑ y, P y * h y with ha
  set b := ∑ y, Q y * h y with hb
  have ha0 : 0 ≤ a := Finset.sum_nonneg fun y _ => hPh y
  have hb0 : 0 ≤ b := Finset.sum_nonneg fun y _ => hQh y
  set D := hellingerSq P Q with hD
  have hD0 : 0 ≤ D := Finset.sum_nonneg fun _ _ => sq_nonneg _
  set u : Y → ℝ := fun y => Real.sqrt (P y) - Real.sqrt (Q y) with hu
  set v : Y → ℝ := fun y => (Real.sqrt (P y) + Real.sqrt (Q y)) * h y with hv
  have hdiff : a - b = ∑ y, u y * v y := by
    rw [ha, hb, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    have e1 := Real.sq_sqrt (hP0 y)
    have e2 := Real.sq_sqrt (hQ0 y)
    simp only [hu, hv]
    linear_combination (-(h y)) * e1 + (h y) * e2
  have hvsum : ∑ y, v y ^ 2 ≤ 2 * R * (a + b) := by
    rw [ha, hb, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_le_sum fun y _ => ?_
    have e1 := Real.sq_sqrt (hP0 y)
    have e2 := Real.sq_sqrt (hQ0 y)
    by_cases hy : 0 < P y ∨ 0 < Q y
    · obtain ⟨h0, hR'⟩ := hh y hy
      have s1 := Real.sqrt_nonneg (P y)
      have s2 := Real.sqrt_nonneg (Q y)
      have h1 : (Real.sqrt (P y) + Real.sqrt (Q y)) ^ 2 ≤ 2 * (P y + Q y) := by
        nlinarith [sq_nonneg (Real.sqrt (P y) - Real.sqrt (Q y))]
      have h2 : h y ^ 2 ≤ R * h y := by nlinarith
      calc v y ^ 2 = (Real.sqrt (P y) + Real.sqrt (Q y)) ^ 2 * h y ^ 2 := by simp only [hv]; ring
        _ ≤ 2 * (P y + Q y) * (R * h y) :=
            mul_le_mul h1 h2 (sq_nonneg _) (by linarith [hP0 y, hQ0 y])
        _ = 2 * R * (P y * h y + Q y * h y) := by ring
    · push_neg at hy
      have hp : P y = 0 := le_antisymm hy.1 (hP0 y)
      have hq : Q y = 0 := le_antisymm hy.2 (hQ0 y)
      simp [hv, hp, hq]
  have hcs : (a - b) ^ 2 ≤ D * ∑ y, v y ^ 2 := by
    rw [hdiff]
    exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u v
  have h94 : |a - b| ≤ Real.sqrt (2 * R * (a + b) * D) := by
    apply Real.abs_le_sqrt
    calc (a - b) ^ 2 ≤ D * ∑ y, v y ^ 2 := hcs
      _ ≤ D * (2 * R * (a + b)) := mul_le_mul_of_nonneg_left hvsum hD0
      _ = 2 * R * (a + b) * D := by ring
  refine ⟨h94, ?_⟩
  have hRD : 0 ≤ R * D := mul_nonneg hR hD0
  have hs : Real.sqrt (2 * R * (a + b) * D) ≤ (a + b) / 2 + R * D := by
    rw [Real.sqrt_le_iff]
    refine ⟨by linarith, ?_⟩
    nlinarith [sq_nonneg ((a + b) / 2 - R * D)]
  have := le_abs_self (a - b)
  nlinarith [this, h94, hs, hRD]
