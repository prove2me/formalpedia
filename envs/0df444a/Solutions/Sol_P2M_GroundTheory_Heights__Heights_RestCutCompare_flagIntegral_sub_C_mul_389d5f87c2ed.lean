-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestCutCompare_flagIntegral_sub_C_mul_389d5f87c2ed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:59:39.658797+00:00
-- url     : https://prove2.me/submissions/d985ec25-eae8-40bb-b440-f4640ae8fcd2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRestCutCompare

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
namespace GroundTheory.Heights₂.Heights
namespace RestCutCompare
theorem _root_.solution (f N : ℕ) (P Q : RestTerms.RootRing f N) (b : ℚ) :
    RestTerms.flagIntegral f N (P - C b * Q) =
      RestTerms.flagIntegral f N P - b * RestTerms.flagIntegral f N Q := by
  unfold RestTerms.flagIntegral
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [coeff_sub, coeff_C_mul]
  ring
end RestCutCompare
end GroundTheory.Heights₂.Heights
