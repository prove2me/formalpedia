-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_joinClosureDeg_comp_5064ccd76e47
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:42:39.478711+00:00
-- url     : https://prove2.me/submissions/8b904641-8476-42cf-9807-cf50403f761b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSegreFlagClosure
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagIndependence
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsPairNumberRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsVerticalDivisorJoinPullback
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSegreFlagClosureBirational
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagIndependenceAlgebra
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSegreFlagClosurePullback
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_joinDeg_comp_closureBlockEquiv_741d524ae234

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
variable {K : Type} {ι : K → Type} {m : ℕ}
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution (ζ : Option (Option K) → ℤ) (L : Fin m → K → ℤ) :
    (fun i => joinClosureDeg ζ L i ∘ closureBlockEquiv K) = closureDeg ζ L := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · simp only [joinClosureDeg, closureDeg, Fin.append_left]
    funext o
    simp
  · simp only [joinClosureDeg, closureDeg, Fin.append_right]
    exact joinDeg_comp_closureBlockEquiv _
end GroundTheory.Heights₂.Heights.NumbersDVR
