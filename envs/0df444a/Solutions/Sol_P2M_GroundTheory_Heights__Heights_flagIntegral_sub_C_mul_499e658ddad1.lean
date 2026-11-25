-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_flagIntegral_sub_C_mul_499e658ddad1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:58:42.502444+00:00
-- url     : https://prove2.me/submissions/cfdd5daa-386d-4a6e-a9f0-e8d399650ac9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRestCutStairNonzero

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
theorem _root_.solution (f N : ℕ) (H S : RestTerms.RootRing f N) (b : ℚ) :
    RestTerms.flagIntegral f N (H - C b * S) =
      RestTerms.flagIntegral f N H - b * RestTerms.flagIntegral f N S := by
  unfold RestTerms.flagIntegral
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [coeff_sub, coeff_C_mul]
  ring
end GroundTheory.Heights₂.Heights
