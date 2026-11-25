-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_extend_inj_25c9cbdc37fc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:24:32.596281+00:00
-- url     : https://prove2.me/submissions/7eef1b7a-4ddf-478e-a9ed-621640d561f5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDivPushForward
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PExistsForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PCutRational
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFDegree
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_extend_apply_self_4752179a6926

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
variable {K K' : Type} (j : K ↪ K') (ι' : K' → Type)
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution {M : Type*} [Zero M] {b₁ b₂ : K → M} :
    Function.extend j b₁ 0 = Function.extend j b₂ 0 ↔ b₁ = b₂ := by
  refine ⟨fun h => funext fun k => ?_, fun h => h ▸ rfl⟩
  have := congrFun h (j k)
  rwa [extend_apply_self, extend_apply_self] at this
end GroundTheory.Heights₂.Heights.FieldNumbers
