-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TheoremB_blockPowerSum_isHomogeneous_4d2f50dbc507
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:22:30.506361+00:00
-- url     : https://prove2.me/submissions/4311937e-137f-46a8-bd67-ac5357d39b5d

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
theorem _root_.solution (f N k : ℕ) (τ : Fin f) :
    (RestTerms.blockPowerSum f N k τ).IsHomogeneous k := by
  unfold RestTerms.blockPowerSum
  exact IsHomogeneous.sum _ _ _ (fun i _ => by simpa using (isHomogeneous_X ℚ (τ, i)).pow k)
end GroundTheory.Heights₂.Heights.TheoremB
