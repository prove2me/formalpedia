-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_HorizontalAvoidingForm_proof_d9953d4d60b8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:07:07.39652+00:00
-- url     : https://prove2.me/submissions/9f6c05e9-db06-4cbc-96dd-9b6c816f48a0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_CutIdentityRightSideCongrOfSubMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ExistsMultiHomogNotMemOfIsRelevant
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_multiHomog_not_mem_finset_9292cb23c465
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_le_and_isRelevant_of_divCycle_ne_zero_6b368bc3dee6


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
universe u
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace HorizontalAvoidingForm
theorem _root_.solution : HorizontalAvoidingForm.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP s hs e
  classical
  have : Infinite O :=
    Infinite.of_injective _ (pow_injective_of_not_isUnit hϖ.not_isUnit hϖ.ne_zero)

  have hfin : (Function.support (divCycle P s)).Finite := by
    apply Set.Finite.subset (Ideal.finite_minimalPrimes_of_isNoetherianRing _ (P ⊔ Ideal.span {s}))
    intro W hW
    by_contra hmin
    apply hW
    unfold divCycle
    rw [dif_neg]
    exact fun h => hmin h.1

  have hT : ∀ Q ∈ insert P (hfin.toFinset.filter fun H => (C ϖ : MRing ι O) ∉ H),
      Q.IsPrime ∧ IsRelevant Q ∧ ∀ a : O, C a ∈ Q → a = 0 := by
    intro Q hQ
    rcases Finset.mem_insert.mp hQ with rfl | hQ
    · refine ⟨hP.multiProj.isPrime, hP.multiProj.relevant, fun a ha => ?_⟩
      have h : a ∈ Q.comap (C : O →+* MRing ι O) := ha
      rw [hP.noTorsion] at h
      exact (Submodule.mem_bot O).mp h
    · obtain ⟨hQs, hϖQ⟩ := Finset.mem_filter.mp hQ
      obtain ⟨hQp, -, hrel⟩ := le_and_isRelevant_of_divCycle_ne_zero
        (Function.mem_support.mp (hfin.mem_toFinset.mp hQs))
      refine ⟨hQp, hrel, fun a ha => ?_⟩
      by_contra ha0
      obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ
      rw [map_mul, map_pow] at ha
      rcases hQp.mem_or_mem ha with h | h
      · exact hQp.ne_top (Ideal.eq_top_of_isUnit_mem _ h (u.isUnit.map C))
      · exact hϖQ (hQp.mem_of_pow_mem _ h)
  obtain ⟨m, hm, hmT⟩ := exists_multiHomog_not_mem_finset e _ hT
  refine ⟨m, hm, hmT P (Finset.mem_insert_self _ _), fun H hH hϖH => hmT H ?_⟩
  exact Finset.mem_insert_of_mem
    (Finset.mem_filter.mpr ⟨hfin.mem_toFinset.mpr (Function.mem_support.mpr hH), hϖH⟩)
end HorizontalAvoidingForm
end GroundTheory.Heights₂.Heights.NumbersDVR
