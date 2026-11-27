-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairJoinRight_proof_88a9de3bed1d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:06:04.156328+00:00
-- url     : https://prove2.me/submissions/ea9efacf-1435-453b-bd7c-d05b69808ad9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsBisTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsMoreAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinFlagPairJoinRight
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairJoinRight_aeval_mid_6cc793cf4f30
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairJoinRight_midDeg_sub_4ada2875cf88
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairJoinRight_isGradedFrame_mid_e03446e74b0b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_Bundles_joinCoord_midVar_3ed08dc9bce4


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing div_mem_chartRing)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg joinCoord restrictChart chartMon IsGradedFrame IsUnitOn FlagPair IsPull
  midDeg midVar joinCoord_midVar)
open FlagPairJoinRight
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace FlagPairJoinRight
theorem _root_.solution (hVert : JoinVerticalDivisorRight.Statement) :
    FlagPairJoinRight.Statement := by
  intro O _ _ _ Ω _ _ K _ ι _ x K' _ ι' _ z K₂ _ ι₂ _ w N V _ _ E E' EF E'F hp hp' φ EB E'B hB hB'
  refine ⟨{
    Vs := φ.Vs
    mono := φ.mono
    dim := φ.dim
    top := φ.top
    deg := fun i => midDeg (K₂ := K₂) (φ.deg i)
    gen := φ.gen
    gen_mem := φ.gen_mem
    frame := isGradedFrame_mid O x z w hp hB φ.frame
    deg' := fun i => midDeg (K₂ := K₂) (φ.deg' i)
    gen' := φ.gen'
    gen'_mem := φ.gen'_mem
    frame' := isGradedFrame_mid O x z w hp' hB' φ.frame'
    f := fun i => rename (midVar ι₂) (φ.f i)
    g := fun i => rename (midVar ι₂) (φ.g i)
    rel := fun i => by
      simp only [aeval_mid]
      exact φ.rel i
    vert := fun i => by
      simp only [midDeg_sub]
      exact hVert O Ω K ι x K' ι' z K₂ ι₂ w _ _ _ (φ.vert i) }, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
end FlagPairJoinRight
end GroundTheory.Heights₂.Heights.NumbersDVR
