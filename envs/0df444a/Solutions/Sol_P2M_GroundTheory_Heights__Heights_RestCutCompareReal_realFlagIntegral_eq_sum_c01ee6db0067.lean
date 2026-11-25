-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestCutCompareReal_realFlagIntegral_eq_sum_c01ee6db0067
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:58:22.572508+00:00
-- url     : https://prove2.me/submissions/72af8997-1253-4e23-9600-0faff77a5180

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
theorem _root_.solution (f N : ℕ) (P : MvPolynomial (Fin f × Fin N) ℝ) :
    realFlagIntegral f N P =
      ∑ α ∈ P.support, realFlagIntegral f N (monomial α (coeff α P)) := by
  unfold realFlagIntegral
  conv_lhs => rw [P.as_sum]
  simp only [coeff_sum, Finset.sum_mul]
  exact Finset.sum_comm
end GroundTheory.Heights₂.Heights.RestCutCompareReal
