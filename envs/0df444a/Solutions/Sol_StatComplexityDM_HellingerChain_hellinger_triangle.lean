-- Prove2me | solution 1 for StatComplexityDM.HellingerChain.hellinger_triangle
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T01:44:10.293998+00:00
-- url     : https://prove2.me/submissions/5738787f-8c68-40eb-96c0-0d987de93159

import Mathlib
import Definitions.Def_FoundationsRL_GeneralDM_Divergences

set_option autoImplicit false
open FoundationsRL.GeneralDM

theorem solution {Y : Type*} [Fintype Y] (P Q R : Y → ℝ)
    (hP : (∀ y, 0 ≤ P y) ∧ ∑ y, P y = 1) (hQ : (∀ y, 0 ≤ Q y) ∧ ∑ y, Q y = 1)
    (hR : (∀ y, 0 ≤ R y) ∧ ∑ y, R y = 1) :
    Real.sqrt (hellingerSq P R) ≤
      Real.sqrt (hellingerSq P Q) + Real.sqrt (hellingerSq Q R) := by
  set a : Y → ℝ := fun y => Real.sqrt (P y) - Real.sqrt (Q y) with ha
  set b : Y → ℝ := fun y => Real.sqrt (Q y) - Real.sqrt (R y) with hb
  have h1 : hellingerSq P R = ∑ y, (a y + b y) ^ 2 := by
    unfold hellingerSq
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [ha, hb]; ring
  have h2 : hellingerSq P Q = ∑ y, a y ^ 2 := rfl
  have h3 : hellingerSq Q R = ∑ y, b y ^ 2 := rfl
  rw [h1, h2, h3]
  have hA : 0 ≤ ∑ y, a y ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hB : 0 ≤ ∑ y, b y ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ a b
  have e : ∑ y, (a y + b y) ^ 2 = ∑ y, a y ^ 2 + 2 * ∑ y, a y * b y + ∑ y, b y ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun y _ => by ring
  rw [e]
  have sA := Real.sq_sqrt hA
  have sB := Real.sq_sqrt hB
  nlinarith [hcs, sA, sB]
