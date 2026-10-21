-- Prove2me | solution 1 for SubsetShrink.L1.h_display
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T04:01:26.7691+00:00
-- url     : https://prove2.me/submissions/0804e126-4ebc-49a2-8616-01c7dbfd0bc9

import Mathlib
import Definitions.Def_SubsetShrink_L1_Model

set_option autoImplicit false
open SubsetShrink.L1

theorem solution {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ)
    (ε : Fin n → ℝ) (βhat β : Fin p → ℝ)
    (σ δ0 lam : ℝ) (hσ : 0 < σ) (hδ0 : 0 < δ0) (hδ1 : δ0 ≤ 1)
    (hp : 1 ≤ p)
    (hlam : lam = 2 * σ * Real.sqrt (2 * Real.log (2 * (p : ℝ))) +
      2 * σ * Real.sqrt (2 * Real.log (1 / δ0))) :
    2 * SubsetShrink.Events.dot ε (X.mulVec (βhat - β)) ≤
      2 * lInf (X.transpose.mulVec ε) * (SubsetShrink.Events.l1 β + SubsetShrink.Events.l1 βhat) ∧
    (ε ∈ SubsetShrink.Events.H X σ δ0 →
      2 * lInf (X.transpose.mulVec ε) * (SubsetShrink.Events.l1 β + SubsetShrink.Events.l1 βhat) ≤
        lam * (SubsetShrink.Events.l1 βhat + SubsetShrink.Events.l1 β)) := by
  have hle : ∀ i, |(X.transpose.mulVec ε) i| ≤ lInf (X.transpose.mulVec ε) := by
    intro i
    unfold lInf
    exact (Finset.le_fold_max _).mpr (Or.inr ⟨i, Finset.mem_univ _, le_rfl⟩)
  have hnn : 0 ≤ lInf (X.transpose.mulVec ε) := by
    unfold lInf
    exact (Finset.le_fold_max _).mpr (Or.inl le_rfl)
  have hl1 : 0 ≤ SubsetShrink.Events.l1 β + SubsetShrink.Events.l1 βhat := by
    unfold SubsetShrink.Events.l1
    positivity
  constructor
  · have hdot : SubsetShrink.Events.dot ε (X.mulVec (βhat - β))
        = ∑ j, (X.transpose.mulVec ε) j * (βhat j - β j) := by
      unfold SubsetShrink.Events.dot
      show ε ⬝ᵥ _ = _
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
      rfl
    have : ∑ j, (X.transpose.mulVec ε) j * (βhat j - β j)
        ≤ lInf (X.transpose.mulVec ε) * (SubsetShrink.Events.l1 β + SubsetShrink.Events.l1 βhat) := by
      unfold SubsetShrink.Events.l1
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j _
      have h1 : (X.transpose.mulVec ε) j * (βhat j - β j)
          ≤ |(X.transpose.mulVec ε) j| * |βhat j - β j| := by
        rw [← abs_mul]; exact le_abs_self _
      have h2 : |βhat j - β j| ≤ |β j| + |βhat j| := by
        calc |βhat j - β j| ≤ |βhat j| + |β j| := abs_sub _ _
          _ = _ := add_comm _ _
      calc _ ≤ |(X.transpose.mulVec ε) j| * |βhat j - β j| := h1
        _ ≤ |(X.transpose.mulVec ε) j| * (|β j| + |βhat j|) :=
          mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
        _ ≤ _ := mul_le_mul_of_nonneg_right (hle j) (by positivity)
    rw [hdot]
    linarith
  · intro hH
    have hH' : lInf (X.transpose.mulVec ε) ≤ σ * Real.sqrt (2 * Real.log (2 * p)) + σ * Real.sqrt (2 * Real.log (1 / δ0)) := by
      have hr : 0 ≤ σ * Real.sqrt (2 * Real.log (2 * p)) + σ * Real.sqrt (2 * Real.log (1 / δ0)) := by positivity
      unfold lInf
      rw [Finset.fold_max_le]
      refine ⟨hr, fun i _ => ?_⟩
      have h3 : |(X.transpose.mulVec ε) i| ≤ SubsetShrink.Events.lInf (X.transpose.mulVec ε) := by
        unfold SubsetShrink.Events.lInf
        exact le_ciSup (f := fun i => |(X.transpose.mulVec ε) i|) (Set.finite_range _).bddAbove i
      exact h3.trans hH
    rw [hlam]
    nlinarith [hH', hl1, mul_le_mul_of_nonneg_right hH' hl1]
