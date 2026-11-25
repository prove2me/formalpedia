-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HermitianBundle_normDegree_eq_deg_sub_462229a1e5e8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:01:01.204478+00:00
-- url     : https://prove2.me/submissions/af4c841f-dd82-4cc8-bd79-c0462e5087c6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Slopes
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PExactSequence
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PChainSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Slopes_PRelSlopeQuot
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermitianBundle_degree_eq_arithDegree_1ab30fd3c0e4


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
open NumberField
noncomputable section
open GroundTheory.Heights₂.Heights.HermitianBundle
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Heights₂.Heights.HermitianBundle
theorem _root_.solution (E : HermitianBundle K) (F : Submodule (𝓞 K) E.carrier) :
    E.normDegree F = (E.sub F).deg := by
  rw [normDegree, deg, degree_eq_arithDegree]
  rfl
end GroundTheory.Heights₂.Heights.HermitianBundle
