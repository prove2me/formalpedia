-- Prove2me | solution 1 for QEC.Coding.SmallSetExpansion.sum_mul_le_of_dyadic_mixing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:46:17.677368+00:00
-- url     : https://prove2.me/submissions/967d0900-3ee8-4a4e-9cee-660e04b5d822

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansion
import Mathlib.Data.Nat.Log
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}
namespace QEC.Coding.SmallSetExpansion
theorem _root_.solution
    [Fintype V] [DecidableEq V]
    (p q : V → Nat) (U : Finset V) (degree : Nat) (lambda : ℝ)
    (sCard tCard : Nat)
    (hLambda : 0 ≤ lambda)
    (hPPos : ∀ x ∈ U, 0 < p x)
    (hPBound : ∀ x ∈ U, p x ≤ degree)
    (hPMix : ∀ A : Finset V, A ⊆ U →
      (∑ x ∈ A, (p x : ℝ)) ≤
        lambda * Real.sqrt ((A.card : ℝ) * sCard))
    (hQMix : ∀ A : Finset V, A ⊆ U →
      (∑ x ∈ A, (q x : ℝ)) ≤
        lambda * Real.sqrt ((A.card : ℝ) * tCard)) :
    (∑ x ∈ U, ((p x * q x : Nat) : ℝ)) ≤
      ((Nat.log 2 degree + 1 : Nat) : ℝ) *
        (2 * lambda ^ 2 * Real.sqrt ((sCard : ℝ) * tCard)) := by
  let level : V → Nat := fun x => Nat.log 2 (p x)
  let levels := Finset.range (Nat.log 2 degree + 1)
  have hLevel : ∀ x ∈ U, level x ∈ levels := by
    intro x hx
    simp only [level, levels, Finset.mem_range]
    exact Nat.lt_succ_of_le (Nat.log_mono_right (hPBound x hx))
  rw [← Finset.sum_fiberwise_of_maps_to hLevel
    (fun x => ((p x * q x : Nat) : ℝ))]
  calc
    (∑ k ∈ levels, ∑ x ∈ U with level x = k,
        ((p x * q x : Nat) : ℝ)) ≤
        ∑ _k ∈ levels,
          2 * lambda ^ 2 * Real.sqrt ((sCard : ℝ) * tCard) := by
      apply Finset.sum_le_sum
      intro k hk
      let A := U.filter fun x => level x = k
      have hAU : A ⊆ U := Finset.filter_subset _ _
      have hLowerNat : 2 ^ k * A.card ≤ ∑ x ∈ A, p x := by
        calc
          2 ^ k * A.card = ∑ _x ∈ A, 2 ^ k := by
            simp [Nat.mul_comm]
          _ ≤ ∑ x ∈ A, p x := by
            apply Finset.sum_le_sum
            intro x hx
            have hxU := hAU hx
            have hxLevel : level x = k := (Finset.mem_filter.mp hx).2
            rw [← hxLevel]
            exact Nat.pow_log_le_self 2 (Nat.ne_of_gt (hPPos x hxU))
      have hUpperNat : ∑ x ∈ A, p x * q x ≤
          2 ^ (k + 1) * ∑ x ∈ A, q x := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro x hx
        apply Nat.mul_le_mul_right
        have hxU := hAU hx
        have hxLevel : level x = k := (Finset.mem_filter.mp hx).2
        exact Nat.le_of_lt (by
          rw [← hxLevel]
          exact Nat.lt_pow_succ_log_self (by omega : 1 < 2) (p x))
      have hPMixA := hPMix A hAU
      have hQMixA := hQMix A hAU
      change (∑ x ∈ A, ((p x * q x : Nat) : ℝ)) ≤
        2 * lambda ^ 2 * Real.sqrt ((sCard : ℝ) * tCard)
      by_cases hAEmpty : A = ∅
      · simp only [hAEmpty, Finset.sum_empty]
        positivity
      have hACardPosNat : 0 < A.card := Finset.card_pos.mpr
        (Finset.nonempty_iff_ne_empty.mpr hAEmpty)
      have hACardPos : (0 : ℝ) < A.card := by exact_mod_cast hACardPosNat
      have hRootAPos : 0 < Real.sqrt (A.card : ℝ) :=
        Real.sqrt_pos.2 hACardPos
      have hLower : ((2 ^ k : Nat) : ℝ) * A.card ≤
          ∑ x ∈ A, (p x : ℝ) := by exact_mod_cast hLowerNat
      have hUpper : (∑ x ∈ A, ((p x * q x : Nat) : ℝ)) ≤
          ((2 ^ (k + 1) : Nat) : ℝ) * ∑ x ∈ A, (q x : ℝ) := by
        exact_mod_cast hUpperNat
      have hRootASq : Real.sqrt (A.card : ℝ) ^ 2 = A.card :=
        Real.sq_sqrt (Nat.cast_nonneg _)
      have hPAfterRoot : ((2 ^ k : Nat) : ℝ) * Real.sqrt A.card ≤
          lambda * Real.sqrt sCard := by
        have hCombined : ((2 ^ k : Nat) : ℝ) * A.card ≤
            lambda * (Real.sqrt A.card * Real.sqrt sCard) := by
          calc
            ((2 ^ k : Nat) : ℝ) * A.card ≤
                ∑ x ∈ A, (p x : ℝ) := hLower
            _ ≤ lambda * Real.sqrt ((A.card : ℝ) * sCard) := hPMixA
            _ = lambda * (Real.sqrt A.card * Real.sqrt sCard) := by
              rw [Real.sqrt_mul (Nat.cast_nonneg A.card)]
        apply (mul_le_mul_iff_of_pos_right hRootAPos).mp
        calc
          ((2 ^ k : Nat) : ℝ) * Real.sqrt A.card * Real.sqrt A.card =
              ((2 ^ k : Nat) : ℝ) * (Real.sqrt A.card) ^ 2 := by ring
          _ = ((2 ^ k : Nat) : ℝ) * A.card := by rw [hRootASq]
          _ ≤ lambda * (Real.sqrt A.card * Real.sqrt sCard) := hCombined
          _ = lambda * Real.sqrt sCard * Real.sqrt A.card := by ring
      calc
        (∑ x ∈ A, ((p x * q x : Nat) : ℝ)) ≤
            ((2 ^ (k + 1) : Nat) : ℝ) * ∑ x ∈ A, (q x : ℝ) := hUpper
        _ = (2 * ((2 ^ k : Nat) : ℝ)) * ∑ x ∈ A, (q x : ℝ) := by
          norm_num [Nat.pow_succ, mul_comm]
        _ ≤ (2 * ((2 ^ k : Nat) : ℝ)) *
            (lambda * Real.sqrt ((A.card : ℝ) * tCard)) :=
          mul_le_mul_of_nonneg_left hQMixA (by positivity)
        _ = (2 * lambda * Real.sqrt tCard) *
            (((2 ^ k : Nat) : ℝ) * Real.sqrt A.card) := by
          rw [Real.sqrt_mul (Nat.cast_nonneg A.card)]
          ring
        _ ≤ (2 * lambda * Real.sqrt tCard) *
            (lambda * Real.sqrt sCard) := by
          exact mul_le_mul_of_nonneg_left hPAfterRoot
            (mul_nonneg (mul_nonneg (by positivity) hLambda)
              (Real.sqrt_nonneg _))
        _ = 2 * lambda ^ 2 * Real.sqrt ((sCard : ℝ) * tCard) := by
          rw [Real.sqrt_mul (Nat.cast_nonneg sCard)]
          ring
    _ = ((Nat.log 2 degree + 1 : Nat) : ℝ) *
        (2 * lambda ^ 2 * Real.sqrt ((sCard : ℝ) * tCard)) := by
      simp [levels]
end QEC.Coding.SmallSetExpansion
