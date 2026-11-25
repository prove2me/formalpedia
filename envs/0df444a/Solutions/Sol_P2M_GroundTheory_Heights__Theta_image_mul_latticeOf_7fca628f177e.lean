-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_image_mul_latticeOf_7fca628f177e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:44:22.533445+00:00
-- url     : https://prove2.me/submissions/c03b556d-965b-4999-8dcb-835d583023a0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmStatements
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmClassReducedParamsNonemptyPf
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_image_mul_span_pair_bc3f8dbd8800

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open UpperHalfPlane ModularGroup Complex NumberField
open scoped Real MatrixGroups nonZeroDivisors
namespace GroundTheory.Heights₂.Theta
theorem _root_.solution (u τ : ℂ) :
    (fun z => u * z) '' latticeOf τ = (Submodule.span ℤ ({u, u * τ} : Set ℂ) : Set ℂ) := by
  rw [latticeOf, image_mul_span_pair, mul_one]
end GroundTheory.Heights₂.Theta
