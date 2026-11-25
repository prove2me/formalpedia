-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_expansion_f69d2f136b96
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:42:12.394614+00:00
-- url     : https://prove2.me/submissions/d4d8fe8f-0c07-4dd2-9870-86aad88fa78f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagIndependence
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagIndependenceAlgebra

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {n : ℕ} (A : MvPolynomial (Fin n) ℤ) :
    ∃ Gs : Fin n → MvPolynomial (Fin n ⊕ Fin n) ℤ,
      rename Sum.inl A - rename Sum.inr A = ∑ i, (X (Sum.inl i) - X (Sum.inr i)) * Gs i := by
  induction A using MvPolynomial.induction_on with
  | C a => exact ⟨0, by simp⟩
  | add p q hp hq =>
    obtain ⟨Ps, hP⟩ := hp
    obtain ⟨Qs, hQ⟩ := hq
    refine ⟨Ps + Qs, ?_⟩
    simp only [map_add, Pi.add_apply, mul_add, Finset.sum_add_distrib, ← hP, ← hQ]
    ring
  | mul_X p j hp =>
    obtain ⟨Ps, hP⟩ := hp
    refine ⟨fun i => X (Sum.inl j) * Ps i + if i = j then rename Sum.inr p else 0, ?_⟩
    simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    have : ∑ i, (X (Sum.inl i) - X (Sum.inr i)) * (X (Sum.inl j) * Ps i) =
        X (Sum.inl j) * ∑ i, (X (Sum.inl i) - X (Sum.inr i)) * Ps i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [this, ← hP]
    simp only [map_mul, rename_X]
    ring
end GroundTheory.Heights₂.Heights.NumbersDVR
