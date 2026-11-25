-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_closureVarEquiv_fst_6eb917874e5f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:41:25.215122+00:00
-- url     : https://prove2.me/submissions/f5b8dab0-a980-4a5c-a789-991b94074d6b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSegreFlagClosure
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagIndependence
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsPairNumberRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsVerticalDivisorJoinPullback
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSegreFlagClosureBirational
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagIndependenceAlgebra
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSegreFlagClosurePullback

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
variable (K : Type*)
variable {K} (ι : K → Type) (M M' : ℕ)
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution (v : Σ o, bundleIdx (bundleIdx ι M) M' o) :
    (closureVarEquiv ι M M' v).1 = closureBlockEquiv K v.1 := by
  rcases v with ⟨_ | (_ | k), l⟩ <;> rfl
end GroundTheory.Heights₂.Heights.NumbersDVR
