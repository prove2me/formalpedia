-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_reverse_ofFn_prod_15f453f2e0cb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:42:49.814456+00:00
-- url     : https://prove2.me/submissions/5814a6be-31b6-4e99-a437-877ab90468de

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_LieCoordinates_SecondKindStatements
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_HsInnerSelfEqSumSq

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
theorem _root_.solution (y : Fin F.dim → ℝ) (τ : Fin F.f) (n : ℕ) :
    ((List.ofFn fun l : Fin n => NormedSpace.exp (yy F y l • Evec F τ l)).reverse).prod =
      G F y τ n := by
  induction n with
  | zero => simp [G]
  | succ m ih =>
    rw [List.ofFn_succ', List.concat_eq_append, List.reverse_append]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
      List.prod_cons]
    simp only [Fin.val_castSucc, Fin.val_last] at ih ⊢
    rw [ih]; rfl
end GroundTheory.Heights₂.Theta.SecondKind.UnitaryRecombination
