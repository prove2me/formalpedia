-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairJoinRight_midChart_extChart_037092772d6a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:34:58.021877+00:00
-- url     : https://prove2.me/submissions/c0c6b771-1daf-4127-88b0-ff4d819d5f7b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsBisTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsMoreAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinFlagPairJoinRight
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
open GroundTheory.Heights₂.Heights.NumbersDVR.FlagPairJoinRight
variable {Ω : Type*} [Field Ω] {K K' K₂ : Type} [Fintype K] [Fintype K'] [Fintype K₂]
  {ι : K → Type} {ι' : K' → Type} {ι₂ : K₂ → Type}
namespace GroundTheory.Heights₂.Heights.NumbersDVR.FlagPairJoinRight
theorem _root_.solution (t : ∀ k : K ⊕ K', Sum.elim ι ι' k) (u : ∀ k, ι₂ k) :
    midChart (extChart t u) = t := by
  funext k
  rcases k with k | k <;> rfl
end GroundTheory.Heights₂.Heights.NumbersDVR.FlagPairJoinRight
