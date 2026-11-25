-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_finrank_le_wittIndex_555afc2a24bc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:54:28.386029+00:00
-- url     : https://prove2.me/submissions/ef67aabb-bdd4-4dd7-beb4-d0b125d59424

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_Parabolic
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_bddAbove_wittIndex_set_241dd391a18f

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
theorem _root_.solution {W : Submodule E (ι → E)} (hW : IsTotallyIsotropic K H W) :
    finrank E W ≤ wittIndex K H :=
  le_csSup bddAbove_wittIndex_set ⟨W, hW, rfl⟩
end GroundTheory.Heights₂.Theta
