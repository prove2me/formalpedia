-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestCutCompareReal_proof_cf8effe3c0aa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:34:01.150776+00:00
-- url     : https://prove2.me/submissions/315eefc3-7b78-4d94-940a-a35e730eb9d7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRestCutCompareReal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestCutCompareReal_realFlagIntegral_monomial_07607d8d68d0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestCutCompareReal_realFlagIntegral_eq_sum_c01ee6db0067
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestCutCompareReal_restRename_monomial_f0b5a4f98cac

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
open MvPolynomial
noncomputable section
open RestCutCompareReal
namespace GroundTheory.Heights₂.Heights
namespace RestCutCompareReal
theorem _root_.solution : RestCutCompareReal.Statement := by
  intro f j k N e I c d hI P hP
  have hmono : ∀ α ∈ P.support, I (restRename f j k N e (monomial α (coeff α P))) =
      c * realFlagIntegral f N (monomial α (coeff α P)) := by
    intro α hα
    have hdeg : (monomial α (1 : ℚ) : RestTerms.RootRing f N).IsHomogeneous d :=
      isHomogeneous_monomial 1 (by
        by_contra h
        exact mem_support_iff.mp hα (hP.coeff_eq_zero h))
    rw [restRename_monomial, map_smul, hI _ hdeg, realFlagIntegral_monomial, smul_eq_mul]
    ring
  have hL : I (restRename f j k N e P) =
      ∑ α ∈ P.support, I (restRename f j k N e (monomial α (coeff α P))) := by
    conv_lhs => rw [P.as_sum]
    rw [map_sum, map_sum]
  rw [hL, realFlagIntegral_eq_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl hmono
end RestCutCompareReal
end GroundTheory.Heights₂.Heights
