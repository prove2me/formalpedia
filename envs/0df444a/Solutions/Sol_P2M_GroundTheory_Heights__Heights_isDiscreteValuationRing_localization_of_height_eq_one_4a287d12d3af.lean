-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_isDiscreteValuationRing_localization_of_height_eq_one_4a287d12d3af
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:32:32.885703+00:00
-- url     : https://prove2.me/submissions/9d365a63-45ed-4c0a-8e4e-84c3b14f5deb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalCodimOneUniformiser
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppAC
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalCodimOneUniformiser

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
theorem _root_.solution {A : Type*} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [IsIntegrallyClosed A] (q : Ideal A) [q.IsPrime] (hq : q.height = 1) :
    IsDiscreteValuationRing (Localization.AtPrime q) := by
  have hbot : q ≠ ⊥ := by
    intro h
    rw [← Ideal.height_eq_zero_iff_eq_bot] at h
    rw [h] at hq
    exact zero_ne_one hq
  have : IsIntegrallyClosed (Localization.AtPrime q) :=
    isIntegrallyClosed_of_isLocalization _ q.primeCompl q.primeCompl_le_nonZeroDivisors
  have : IsNoetherianRing (Localization.AtPrime q) :=
    IsLocalization.isNoetherianRing q.primeCompl _ inferInstance
  have hdim : ringKrullDim (Localization.AtPrime q) = 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height q, hq]
    rfl
  have : Ring.KrullDimLE 1 (Localization.AtPrime q) := by
    rw [Ring.krullDimLE_iff, hdim]
    rfl
  have hnf : ¬ IsField (Localization.AtPrime q) := IsLocalization.AtPrime.not_isField A hbot _
  have huniq : ∃! P : Ideal (Localization.AtPrime q), P ≠ ⊥ ∧ P.IsPrime := by
    refine ⟨maximalIdeal (Localization.AtPrime q), ?_, fun P hP => ?_⟩
    · exact And.intro (isField_iff_maximalIdeal_eq.not.mp hnf) inferInstance
    have : P.IsPrime := hP.2
    exact IsLocalRing.eq_maximalIdeal (this.isMaximal_of_ne_bot hP.1)
  have h3 : IsIntegrallyClosed (Localization.AtPrime q) ∧
      ∃! P : Ideal (Localization.AtPrime q), P ≠ ⊥ ∧ P.IsPrime := And.intro inferInstance huniq
  exact ((IsDiscreteValuationRing.TFAE (Localization.AtPrime q) hnf).out 0 3).mpr h3
end GroundTheory.Heights₂.Heights
