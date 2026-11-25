-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_mem_orth_fb4b4d3fb1a7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:43:10.050836+00:00
-- url     : https://prove2.me/submissions/845e728f-59c2-440f-b93b-ec3015880cac

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_Parabolic

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
namespace GroundTheory.Heights₂.Theta
theorem _root_.solution {W : Submodule E (ι → E)} {y : ι → E} :
    y ∈ orth K H W ↔ ∀ x ∈ W, hermPair K H x y = 0 := Iff.rfl
end GroundTheory.Heights₂.Theta
