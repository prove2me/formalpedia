-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_I_mem_latticeReducedParams_de4ca370e9c4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:10:46.635552+00:00
-- url     : https://prove2.me/submissions/c634eebd-eba6-4809-b056-c928bd70a488

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmStatements
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_I_mem_fd_693a9f63e115

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
theorem _root_.solution :
    UpperHalfPlane.I ∈ latticeReducedParams (latticeOf Complex.I) :=
  ⟨I_mem_fd, 1, one_ne_zero, by simp [UpperHalfPlane.I]⟩
end GroundTheory.Heights₂.Theta
