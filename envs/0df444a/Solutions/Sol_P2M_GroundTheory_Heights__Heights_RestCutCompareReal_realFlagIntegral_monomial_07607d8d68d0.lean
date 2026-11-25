-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestCutCompareReal_realFlagIntegral_monomial_07607d8d68d0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:58:27.024068+00:00
-- url     : https://prove2.me/submissions/ee6f0f9d-1bc3-49d2-bb1d-b9963f4c873f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRestCutCompareReal

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
open GroundTheory.Heights₂.Heights.RestCutCompareReal
namespace GroundTheory.Heights₂.Heights.RestCutCompareReal
theorem _root_.solution (f N : ℕ) (α : Fin f × Fin N →₀ ℕ) (r : ℝ) :
    realFlagIntegral f N (monomial α r) =
      r * (RestTerms.flagIntegral f N (monomial α (1 : ℚ)) : ℝ) := by
  unfold realFlagIntegral RestTerms.flagIntegral
  rw [Rat.cast_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [coeff_monomial, coeff_monomial]
  split_ifs <;> push_cast <;> ring
end GroundTheory.Heights₂.Heights.RestCutCompareReal
