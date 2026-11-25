-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_isRegularLocalRing_of_height_eq_one_249010c076d9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:45:24.270036+00:00
-- url     : https://prove2.me/submissions/35aaa2c3-53d0-44bb-81ab-6bf813cfb482

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalCodimOneCompleteIntersection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_RegularQuotientGenerators
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLocalizationAtPrimeQuotient
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppAC
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalCodimOneCompleteIntersection

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial IsLocalRing
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] (q : Ideal A) [q.IsPrime] (hq : q.height = 1) {C : Type*} [CommRing C]
    (eqv : Localization.AtPrime (maximalIdeal (Localization.AtPrime q)) ≃+* C) :
    IsRegularLocalRing C ∧ ringKrullDim C = 1 := by
  have : IsDomain (Localization.AtPrime q) :=
    IsLocalization.isDomain_localization (Ideal.primeCompl_le_nonZeroDivisors q)
  have : IsIntegrallyClosed (Localization.AtPrime q) :=
    isIntegrallyClosed_of_isLocalization _ q.primeCompl (Ideal.primeCompl_le_nonZeroDivisors q)
  have hdB : ringKrullDim (Localization.AtPrime q) = 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height q, hq]
    rfl
  have : Ring.KrullDimLE 1 (Localization.AtPrime q) := Ring.krullDimLE_iff.mpr (by rw [hdB]; rfl)
  have h3 : IsIntegrallyClosed (Localization.AtPrime q) ∧
      ∀ p : Ideal (Localization.AtPrime q), p ≠ ⊥ → p.IsPrime → p = maximalIdeal (Localization.AtPrime q) :=
    ⟨inferInstance, fun p hp0 hpp => eq_maximalIdeal (hpp.isMaximal_of_ne_bot hp0)⟩
  have : IsDedekindDomain (Localization.AtPrime q) :=
    ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain (Localization.AtPrime q)).out 3 2).mp h3
  refine ⟨IsRegularLocalRing.of_ringEquiv eqv, ?_⟩
  rw [← ringKrullDim_eq_of_ringEquiv eqv,
    IsLocalization.AtPrime.ringKrullDim_eq_height (maximalIdeal (Localization.AtPrime q))
      (Localization.AtPrime (maximalIdeal (Localization.AtPrime q))),
    IsLocalRing.maximalIdeal_height_eq_ringKrullDim, hdB]
end GroundTheory.Heights₂.Heights
