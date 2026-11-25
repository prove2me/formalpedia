-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_isHomogeneous_pairDiff_7f3a95024044
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:33:13.893541+00:00
-- url     : https://prove2.me/submissions/d4745c10-667e-4482-921b-07dd8e587e1a

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
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution (i : Fin n) : (pairDiff i).IsHomogeneous 1 :=
  (isHomogeneous_X _ _).sub (isHomogeneous_X _ _)
end GroundTheory.Heights₂.Heights.NumbersDVR
