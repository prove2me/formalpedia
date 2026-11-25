-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_orth_antitone_7a7d283f0c36
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:34:09.494056+00:00
-- url     : https://prove2.me/submissions/df36891b-d011-4d19-bd9a-a0ddf3636b56

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
theorem _root_.solution {W W' : Submodule E (ι → E)} (h : W ≤ W') : orth K H W' ≤ orth K H W :=
  fun _ hy x hx => hy x (h hx)
end GroundTheory.Heights₂.Theta
