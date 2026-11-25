-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_vNumL_eq_foldr_3c1ed327871b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:59:13.758659+00:00
-- url     : https://prove2.me/submissions/625cd7ba-430b-414c-8cc7-b7354a2d0aaa

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagIndependenceAlgebra
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMixedDiffLinear
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_OfSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPairNumberExpansionKoszul

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
noncomputable section
variable {K : Type*} [DecidableEq K] {ι : K → Type*}
  {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution (W : Ideal (MRing ι O)) (l : List (K → ℤ)) :
    vNumL W l = eventualValue (l.foldr diffStep (hilbFn (specialIdeal W))) := by
  unfold vNumL vNum intNum mixedDiff
  rw [List.ofFn_get]
end GroundTheory.Heights₂.Heights.NumbersDVR
