-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_I_mem_fd_693a9f63e115
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:42:36.249228+00:00
-- url     : https://prove2.me/submissions/b92bc2e0-d25f-4fa9-9365-6b5e49e98c31

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmStatements

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
open UpperHalfPlane ModularGroup ModularForm Complex NumberField
open scoped Real Modular MatrixGroups nonZeroDivisors
namespace GroundTheory.Heights₂.Theta
theorem _root_.solution : UpperHalfPlane.I ∈ 𝒟 := by
  refine ⟨?_, ?_⟩
  · simp [UpperHalfPlane.I, Complex.normSq_I]
  · simp [UpperHalfPlane.I]
end GroundTheory.Heights₂.Theta
