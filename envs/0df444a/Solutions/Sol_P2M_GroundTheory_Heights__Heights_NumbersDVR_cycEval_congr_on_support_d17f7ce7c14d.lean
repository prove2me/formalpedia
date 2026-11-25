-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_cycEval_congr_on_support_d17f7ce7c14d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:41:28.057625+00:00
-- url     : https://prove2.me/submissions/e9916923-0d89-4d35-a161-00819f18d98d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BlowUpPushHypothesesExample
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_CycEvalCongrOnSupport

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
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type} {R : Type*} [CommRing R]
omit [Fintype K] [DecidableEq K]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {n n' : Ideal (MRing ι R) → ℤ} (Z : Ideal (MRing ι R) → ℤ)
    (h : ∀ W, Z W ≠ 0 → n W = n' W) : cycEval n Z = cycEval n' Z := by
  unfold cycEval
  refine finsum_congr fun W => ?_
  by_cases hW : Z W = 0
  · rw [hW, zero_mul, zero_mul]
  · rw [h W hW]
end GroundTheory.Heights₂.Heights.NumbersDVR
