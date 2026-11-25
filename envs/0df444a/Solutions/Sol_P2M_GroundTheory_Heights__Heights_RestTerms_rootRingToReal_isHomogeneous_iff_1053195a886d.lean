-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_isHomogeneous_iff_1053195a886d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:13:22.843411+00:00
-- url     : https://prove2.me/submissions/9103456b-ab1a-4bba-88cc-ad6e2317a066

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsFlagIntegralOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PHomogeneousComponentMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsPowerSumDecompositionHomogeneousComponent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms
theorem _root_.solution (f N j k : ℕ) (h : N = j + k) (P : RootRing f N) (n : ℕ) :
    (rootRingToReal f N j k h P).IsHomogeneous n ↔ P.IsHomogeneous n := by
  rw [rootRingToReal, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    IsHomogeneous.rename_isHomogeneous_iff
      (Function.Injective.prodMap Function.injective_id (finCongr h).injective)]
  constructor
  · intro hP d hd
    apply hP
    rw [coeff_map]
    exact (map_ne_zero_iff _ (algebraMap ℚ ℝ).injective).mpr hd
  · intro hP
    exact hP.map _
end GroundTheory.Heights₂.Heights.RestTerms
