-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_isTotallyIsotropic_bot_8ca3445bf569
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:44:33.503566+00:00
-- url     : https://prove2.me/submissions/ac85bd1a-ec2d-42fe-86c3-d592803ddcae

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_Parabolic
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_hermPair_zero_left_236801a17ead

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open Module Matrix TensorProduct GroundTheory.Automorphic NumberField
open scoped NumberField.AdeleRing
noncomputable section
set_option linter.unusedSectionVars false
open scoped Classical
variable {K E : Type*} [Field K] [Field E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (K) (H : Matrix ι ι E)
variable {K H}
variable (K H)
variable {K H}
variable (K H)
variable {K H}
namespace GroundTheory.Heights₂.Theta
theorem _root_.solution : IsTotallyIsotropic K H (⊥ : Submodule E (ι → E)) := by
  intro x hx y _
  rw [Submodule.mem_bot] at hx
  rw [hx]
  exact hermPair_zero_left y
end GroundTheory.Heights₂.Theta
