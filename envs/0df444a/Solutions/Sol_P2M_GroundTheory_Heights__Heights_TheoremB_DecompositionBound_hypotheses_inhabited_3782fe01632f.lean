-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TheoremB_DecompositionBound_hypotheses_inhabited_3782fe01632f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:46:37.015383+00:00
-- url     : https://prove2.me/submissions/41a725e9-ba8a-4917-9322-cfc1997c7b09

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MultinomialWeights_Statements
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TheoremB_unitWallFamily_isWallFamily_9e2b16c63f10
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TheoremB_exists_complement_of_le_976f1511e062
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TheoremB_uSpace_le_vSpace_rankTwo_25fcee178a13

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
namespace DecompositionBound
theorem _root_.solution :
    IsWallFamily d1 (unitWallFamily d1) ∧
      ∃ V' : Submodule ℝ (LamPoly d1), V' ≤ vSpace d1 ∧ Disjoint (uSpace d1) V' ∧
        uSpace d1 ⊔ V' = vSpace d1 :=
  ⟨unitWallFamily_isWallFamily d1, exists_complement_of_le uSpace_le_vSpace_rankTwo⟩
end DecompositionBound
end GroundTheory.Heights₂.Heights.TheoremB
