-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbEventuallyPoly_hilbFn_eq_zero_of_block_4ff705798091
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:52:03.058047+00:00
-- url     : https://prove2.me/submissions/afbfaaf4-a285-4aab-9767-8cb53dda31cb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_HilbEventuallyPolyQualified

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.FieldNumbers.HilbEventuallyPoly
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {F : Type*} [Field F]
attribute [local instance] MvPolynomial.weightedGradedAlgebra
namespace GroundTheory.Heights₂.Heights.FieldNumbers.HilbEventuallyPoly
theorem _root_.solution {I : Ideal (MRing ι F)} (k : K)
    (hk : ∀ i, (X ⟨k, i⟩ : MRing ι F) ∈ I) (m : K → ℤ) (hm : 1 ≤ m k) : hilbFn I m = 0 := by
  unfold hilbFn
  split_ifs with h
  · have hbot : gradedPiece I (fun k => (m k).toNat) = ⊥ := by
      rw [gradedPiece, eq_bot_iff, Submodule.map_le_iff_le_comap]
      intro f hf
      rw [Submodule.mem_comap, Submodule.mem_bot, AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk,
        Ideal.Quotient.eq_zero_iff_mem]
      rw [mem_weightedHomogeneousSubmodule] at hf
      rw [f.as_sum]
      refine Ideal.sum_mem _ fun d hd => ?_
      have hw := hf (mem_support_iff.mp hd)
      obtain ⟨i, hi⟩ : ∃ i, d ⟨k, i⟩ ≠ 0 := by
        by_contra hcon
        simp only [not_exists, ne_eq, not_not] at hcon
        have h0 : Finsupp.weight (blockWeight ι) d k = 0 := by
          rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
          refine Finset.sum_eq_zero fun v _ => ?_
          obtain ⟨k', i'⟩ := v
          simp only [blockWeight, Pi.smul_apply, smul_eq_mul]
          by_cases hkk : k' = k
          · subst hkk
            simp [hcon i']
          · simp [Ne.symm hkk]
        rw [hw] at h0
        simp only at h0
        omega
      have hmono : monomial d (coeff d f) =
          X ⟨k, i⟩ * monomial (d - Finsupp.single ⟨k, i⟩ 1) (coeff d f) := by
        rw [X, monomial_mul, one_mul, add_tsub_cancel_of_le]
        rw [Finsupp.single_le_iff]
        omega
      rw [hmono]
      exact Ideal.mul_mem_right _ _ (hk i)
    rw [hbot, finrank_bot]
    simp
  · rfl
end GroundTheory.Heights₂.Heights.FieldNumbers.HilbEventuallyPoly
