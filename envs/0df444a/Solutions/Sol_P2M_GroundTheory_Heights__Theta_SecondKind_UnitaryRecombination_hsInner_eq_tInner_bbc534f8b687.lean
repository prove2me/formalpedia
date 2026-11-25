-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_hsInner_eq_tInner_bbc534f8b687
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:56:15.556883+00:00
-- url     : https://prove2.me/submissions/72cb3493-f20b-49ec-9df7-4a9bac0e2895

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_LieCoordinates_SecondKindStatements
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_HsInnerSelfEqSumSq
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_hsInner_eq_1ad3b1c0ab1b
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_E_apply_of_ne_3d49cd00040c
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_tInner_zero_left_0d082ca806b0

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
variable {ι : Type*} [Fintype ι]
variable (F : OrthoFrame)
namespace GroundTheory.Heights₂.Theta.SecondKind.UnitaryRecombination
theorem _root_.solution {k : Fin F.dim} {τ : Fin F.f} (hk : F.place k = τ) (X : MatProd F.p F.q) :
    hsInner (F.E k) X = tInner (F.E k τ) (X τ) := by
  rw [hsInner_eq, Finset.sum_eq_single τ]
  · intro τ' _ h
    rw [E_apply_of_ne F (fun h' => h (h'.trans hk)), tInner_zero_left]
  · simp
end GroundTheory.Heights₂.Theta.SecondKind.UnitaryRecombination
