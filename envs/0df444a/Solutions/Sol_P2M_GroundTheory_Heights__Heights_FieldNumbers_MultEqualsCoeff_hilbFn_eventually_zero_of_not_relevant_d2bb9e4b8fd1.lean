-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_MultEqualsCoeff_hilbFn_eventually_zero_of_not_relevant_d2bb9e4b8fd1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:22:45.322329+00:00
-- url     : https://prove2.me/submissions/45435a79-3b16-4366-b56b-b88c08b8b3a3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegreeBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PMultEqualsCoeff

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
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR Filter
universe u
open GroundTheory.Heights₂.Heights.FieldNumbers.MultEqualsCoeff
variable {K : Type*}
variable [Fintype K] [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]
namespace GroundTheory.Heights₂.Heights.FieldNumbers.MultEqualsCoeff
theorem _root_.solution (I : Ideal (MRing ι F)) (hI : ¬ IsRelevant I) :
    ∀ᶠ m in atTop, hilbFn I m = 0 := by
  simp only [IsRelevant, not_forall, not_exists, not_not] at hI
  obtain ⟨k, hk⟩ := hI
  filter_upwards [eventually_ge_atTop (1 : K → ℤ)] with m hm
  unfold hilbFn
  split_ifs with h0
  · have hbot : gradedPiece I (fun k => (m k).toNat) = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨f, hf, rfl⟩
      rw [Submodule.mem_bot, AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk,
        Ideal.Quotient.eq_zero_iff_mem, MvPolynomial.as_sum f]
      refine Ideal.sum_mem _ fun s hs => ?_
      have hw := (mem_weightedHomogeneousSubmodule _ _ _ _).mp hf (mem_support_iff.mp hs)
      obtain ⟨v, hv, hvk⟩ : ∃ v ∈ s.support, v.1 = k := by
        by_contra hne
        simp only [not_exists, not_and] at hne
        have h1 := congrFun hw k
        rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply,
          Finset.sum_eq_zero fun v hv => by
            simp [blockWeight, Ne.symm (hne v hv)]] at h1
        have := hm k
        simp only [Pi.one_apply] at this
        omega
      have hle : Finsupp.single v 1 ≤ s := by
        rw [Finsupp.single_le_iff]
        exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hv)
      have hX : (X v : MRing ι F) ∈ I := by
        obtain ⟨k', i⟩ := v
        subst hvk
        exact hk i
      have e : monomial s (coeff s f) = X v * monomial (s - Finsupp.single v 1) (coeff s f) := by
        rw [show (X v : MRing ι F) = monomial (Finsupp.single v 1) 1 from rfl, monomial_mul,
          one_mul, add_tsub_cancel_of_le hle]
      rw [e]
      exact I.mul_mem_right _ hX
    rw [hbot]
    simp
  · rfl
end GroundTheory.Heights₂.Heights.FieldNumbers.MultEqualsCoeff
