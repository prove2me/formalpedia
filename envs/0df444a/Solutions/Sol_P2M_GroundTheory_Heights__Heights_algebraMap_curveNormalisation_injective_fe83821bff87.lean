-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_algebraMap_curveNormalisation_injective_fe83821bff87
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:48:52.024487+00:00
-- url     : https://prove2.me/submissions/697de39c-bf2a-41a8-81b7-b50c1536ec39

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveNormalisationLength

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
open MvPolynomial ComplexSets
noncomputable section
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) :
    Function.Injective (algebraMap (curveLocalRing I q) (curveNormalisation I q)) := by
  intro a b h
  exact IsLocalization.injective (FractionRing (curveLocalRing I q)) le_rfl (congrArg Subtype.val h)
end GroundTheory.Heights₂.Heights
