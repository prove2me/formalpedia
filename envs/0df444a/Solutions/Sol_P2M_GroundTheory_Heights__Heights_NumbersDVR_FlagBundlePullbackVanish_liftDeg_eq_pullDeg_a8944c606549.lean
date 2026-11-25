-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundlePullbackVanish_liftDeg_eq_pullDeg_a8944c606549
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:06:47.884918+00:00
-- url     : https://prove2.me/submissions/a659845d-002d-40cb-9539-eb4f6444385d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagBundle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagBundlePullbackVanish

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.FlagBundlePullbackVanish
namespace GroundTheory.Heights₂.Heights.NumbersDVR.FlagBundlePullbackVanish
theorem _root_.solution {K : Type*} (L : K → ℤ) :
    liftDeg L = FieldNumbers.pullDeg Function.Embedding.some L := by
  funext o
  cases o with
  | none =>
    rw [FieldNumbers.pullDeg, Function.extend_apply' _ _ _ (by simp)]
    rfl
  | some k =>
    exact (Function.Embedding.some.injective.extend_apply L 0 k).symm
end GroundTheory.Heights₂.Heights.NumbersDVR.FlagBundlePullbackVanish
