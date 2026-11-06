-- Prove2me | solution 1 for PrimalDualLDR.FixedRecourse.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T17:41:09.671077+00:00
-- url     : https://prove2.me/submissions/e1d7b81f-12e6-4ba8-99ab-2f3462b84093

import Mathlib
import Definitions.Def_PrimalDualLDR_FixedRecourse_Basic
import Definitions.Def_PrimalDualLDR_FixedRecourse_Setting
import Definitions.Def_PrimalDualLDR_FixedRecourse_Problems
import Theorems.Thm_LinearOptimization_farkas_inequality_form

open MeasureTheory Matrix

open PrimalDualLDR.FixedRecourse in
theorem solution {k l : ℕ} (W : Matrix (Fin l) (Fin k) ℝ) (h : Fin l → ℝ)
    (hne : (polyhedron W h).Nonempty) (z : Fin k → ℝ) :
    (∀ ξ ∈ polyhedron W h, 0 ≤ z ⬝ᵥ ξ) ↔
      ∃ lam : Fin l → ℝ, (∀ i, 0 ≤ lam i) ∧ Wᵀ.mulVec lam = z ∧ 0 ≤ h ⬝ᵥ lam := by
  have key := LinearOptimization.farkas_inequality_form (-W) (-h) (-z) 0
    (by
      obtain ⟨x, hx⟩ := hne
      refine ⟨x, fun i => ?_⟩
      have := hx i
      simp only [neg_mulVec, Pi.neg_apply]
      linarith)
  have hmem : ∀ ξ, ξ ∈ polyhedron W h ↔ (-W).mulVec ξ ≤ -h := by
    intro ξ
    simp only [polyhedron, Set.mem_setOf_eq, neg_mulVec, Pi.le_def, Pi.neg_apply, neg_le_neg_iff]
  constructor
  · intro H
    obtain ⟨p, hp0, hpA, hpb⟩ := key.1 (fun x hx => by
      have := H x ((hmem x).2 hx)
      simp only [neg_dotProduct]; linarith)
    refine ⟨p, fun i => hp0 i, ?_, ?_⟩
    · have : (-W)ᵀ.mulVec p = -(Wᵀ.mulVec p) := by
        rw [transpose_neg, neg_mulVec]
      rw [this] at hpA
      exact neg_inj.1 hpA
    · rw [dotProduct_neg] at hpb
      rw [dotProduct_comm]; linarith
  · rintro ⟨lam, hl0, hlW, hlh⟩ ξ hξ
    rw [← hlW, mulVec_transpose, ← dotProduct_mulVec]
    have h1 : lam ⬝ᵥ h ≤ lam ⬝ᵥ W.mulVec ξ := by
      unfold dotProduct
      exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hξ i) (hl0 i)
    rw [dotProduct_comm] at hlh
    linarith
