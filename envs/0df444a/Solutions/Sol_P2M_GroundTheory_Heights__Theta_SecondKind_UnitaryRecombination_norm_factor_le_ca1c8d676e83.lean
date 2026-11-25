-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_norm_factor_le_ca1c8d676e83
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:57:51.837567+00:00
-- url     : https://prove2.me/submissions/e91af37e-23cb-4a72-86f2-ac72fd9992bd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_LieCoordinates_SecondKindStatements
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_HsInnerSelfEqSumSq
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_E_apply_of_ne_3d49cd00040c
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_norm_Evec_le_81ad8f9d2021

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
open Matrix GroundTheory.Automorphic
open scoped Matrix.Norms.L2Operator
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Theta.SecondKind
open GroundTheory.Heights₂.Theta.SecondKind.UnitaryRecombination
variable (F : OrthoFrame)
namespace GroundTheory.Heights₂.Theta.SecondKind.UnitaryRecombination
theorem _root_.solution (y : Fin F.dim → ℝ) (τ : Fin F.f) (m : ℕ) :
    ‖yy F y m • Evec F τ m‖ ≤ cc F y τ m := by
  rw [norm_smul]
  unfold yy cc Evec
  split_ifs with h h'
  · rw [Real.norm_eq_abs]
    have := norm_Evec_le F τ m
    rw [Evec, dif_pos h] at this
    nlinarith [abs_nonneg (y ⟨m, h⟩)]
  · rw [E_apply_of_ne F (Ne.symm h')]; simp
  · simp
end GroundTheory.Heights₂.Theta.SecondKind.UnitaryRecombination
