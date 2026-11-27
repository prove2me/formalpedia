-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_hermPair_eq_zero_comm_f643118d2e0b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:13:19.423112+00:00
-- url     : https://prove2.me/submissions/8b141364-d44e-43f5-b00f-96e7d198ce51

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_Parabolic
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_hermPair_comm_dfd82cefa166
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.conj_conj



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
namespace GroundTheory.Heights₂.Theta
theorem _root_.solution (hH : IsHermitianFor (conjHom K E) H) {x y : ι → E} :
    hermPair K H y x = 0 ↔ hermPair K H x y = 0 := by
  rw [hermPair_comm hH]
  constructor
  · intro h
    have := congrArg (conj K E) h
    rwa [conj_conj, map_zero] at this
  · intro h
    rw [h, map_zero]
end GroundTheory.Heights₂.Theta
