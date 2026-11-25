-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TheoremB_invForms_le_homogeneous_72bab69dee43
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:22:37.495705+00:00
-- url     : https://prove2.me/submissions/1524e0f3-4942-403d-8129-3990f68a1043

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
theorem _root_.solution : invForms d ≤ homogeneousSubmodule (Idx d) ℝ 1 := by
  rw [invForms, Submodule.span_le]
  rintro P (⟨τ, rfl⟩ | ⟨τ, rfl⟩)
  · exact (mem_homogeneousSubmodule _ _).2
      (IsHomogeneous.sum _ _ _ (fun i _ => isHomogeneous_X ℝ _))
  · exact (mem_homogeneousSubmodule _ _).2
      (IsHomogeneous.sum _ _ _ (fun i _ => isHomogeneous_X ℝ _))
end GroundTheory.Heights₂.Heights.TheoremB
