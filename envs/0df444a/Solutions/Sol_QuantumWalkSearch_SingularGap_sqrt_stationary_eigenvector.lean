-- Prove2me | solution 1 for QuantumWalkSearch.SingularGap.sqrt_stationary_eigenvector
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T12:11:19.538978+00:00
-- url     : https://prove2.me/submissions/ac7cd124-4c12-43bd-88f7-97e5079ad549

import Mathlib
import Definitions.Def_QuantumWalkSearch_SingularGap_Discriminant

open QuantumWalkSearch.SingularGap
open Matrix

theorem solution {X : Type*} [Fintype X] [DecidableEq X]
    (P : Matrix X X ℝ) (π : X → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ X) (hirr : P.IsIrreducible)
    (hπ : IsStationaryDistribution P π) :
    discriminant P π *ᵥ (sqrtStationary π).ofLp = (sqrtStationary π).ofLp ∧
      (sqrtStationary π).ofLp ᵥ* discriminant P π = (sqrtStationary π).ofLp := by
  have hs : ∀ x, 0 < Real.sqrt (π x) := fun x => Real.sqrt_pos.mpr (hπ.pos x)
  have hrow : ∀ x, ∑ y, Real.sqrt (π x) * P x y / Real.sqrt (π y) * Real.sqrt (π y) = Real.sqrt (π x) := by
    intro x
    have : ∀ y, Real.sqrt (π x) * P x y / Real.sqrt (π y) * Real.sqrt (π y) = Real.sqrt (π x) * P x y :=
      fun y => div_mul_cancel₀ _ (hs y).ne'
    simp only [this]
    rw [← Finset.mul_sum, Matrix.sum_row_of_mem_rowStochastic hP x, mul_one]
  have hcol : ∀ y, ∑ x, Real.sqrt (π x) * (Real.sqrt (π x) * P x y / Real.sqrt (π y)) = Real.sqrt (π y) := by
    intro y
    have : ∀ x, Real.sqrt (π x) * (Real.sqrt (π x) * P x y / Real.sqrt (π y))
        = π x * P x y / Real.sqrt (π y) := by
      intro x
      rw [← mul_div_assoc, ← mul_assoc, Real.mul_self_sqrt (hπ.pos x).le]
    simp only [this]
    rw [← Finset.sum_div, hπ.stationary y, Real.div_sqrt]
  constructor
  · funext x
    simp only [mulVec, dotProduct, discriminant, sqrtStationary, of_apply]
    conv_rhs => rw [← hrow x]
    push_cast
    rfl
  · funext y
    simp only [vecMul, dotProduct, discriminant, sqrtStationary, of_apply]
    conv_rhs => rw [← hcol y]
    push_cast
    rfl
