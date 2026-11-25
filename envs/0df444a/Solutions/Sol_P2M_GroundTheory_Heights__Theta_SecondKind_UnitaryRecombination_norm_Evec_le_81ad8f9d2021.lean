-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_norm_Evec_le_81ad8f9d2021
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:49:55.838181+00:00
-- url     : https://prove2.me/submissions/b7d603ff-4369-4da7-90c2-e5528660660b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_LieCoordinates_SecondKindStatements
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_HsInnerSelfEqSumSq
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_hs_nonneg_1a2c98d71290
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_opNorm_le_hs_b2250fdb08b7
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_hsInner_self_746aeee08685

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
theorem _root_.solution (τ : Fin F.f) (m : ℕ) : ‖Evec F τ m‖ ≤ 1 := by
  unfold Evec; split_ifs with h
  · refine (opNorm_le_hs _).trans ?_
    have h1 : hsInner (F.E ⟨m, h⟩) (F.E ⟨m, h⟩) = 1 := by simp [F.orthonormal]
    rw [hsInner_self] at h1
    have h2 : hs (F.E ⟨m, h⟩ τ) ^ 2 ≤ 1 := by
      rw [← h1]
      exact Finset.single_le_sum (f := fun τ' => hs (F.E ⟨m, h⟩ τ') ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ τ)
    nlinarith [hs_nonneg (F.E ⟨m, h⟩ τ)]
  · simp
end GroundTheory.Heights₂.Theta.SecondKind.UnitaryRecombination
