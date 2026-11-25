-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_IsTotallyIsotropic_le_orth_45a92c67c747
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:42:41.415909+00:00
-- url     : https://prove2.me/submissions/072d235e-3833-4c1a-8b66-327448692e3e

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
variable (K H)
variable {K H}
namespace GroundTheory.Heights₂.Theta
namespace IsTotallyIsotropic
theorem _root_.solution {W : Submodule E (ι → E)} (hW : IsTotallyIsotropic K H W) :
    W ≤ orth K H W :=
  fun y hy x hx => hW x hx y hy
end IsTotallyIsotropic
end GroundTheory.Heights₂.Theta
