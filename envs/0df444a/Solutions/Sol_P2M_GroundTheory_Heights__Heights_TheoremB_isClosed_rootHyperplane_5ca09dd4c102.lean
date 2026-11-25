-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TheoremB_isClosed_rootHyperplane_5ca09dd4c102
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:22:01.901476+00:00
-- url     : https://prove2.me/submissions/4e115642-974e-4251-abf9-ee60979caa06

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MultinomialWeights_Statements

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.TheoremB
open MvPolynomial Finset
variable (d : IndexData)
namespace GroundTheory.Heights₂.Heights.TheoremB
theorem _root_.solution (τ : Fin d.f) (a b : Fin d.N) : IsClosed (rootHyperplane d τ a b) :=
  isClosed_eq (continuous_apply _) (continuous_apply _)
end GroundTheory.Heights₂.Heights.TheoremB
