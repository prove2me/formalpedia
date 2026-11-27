-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_hsVec_sub_1075cf7fe718
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:22:26.04186+00:00
-- url     : https://prove2.me/submissions/103b9c9c-5209-4a28-957f-03365d1c0fb6

import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_HsInnerSelfEqSumSq
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_LieCoordinates_SecondKindStatements
import Mathlib
import Mathlib.Tactic



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
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
theorem _root_.solution (X Y : Matrix ι ι ℂ) : hsVec (X - Y) = hsVec X - hsVec Y := by
  first
    | (intros; rfl)
    | (intros; ext; rfl)
    | (intros; exact LinearMap.ext fun _ => rfl)
    | (intros; apply Subtype.ext; rfl)
    | (intros; infer_instance)
    | (refine ⟨?_, ?_⟩ <;> infer_instance)
    | (intros; ext; simp; done)
    | (intros; assumption)
    | (intros; omega)
    | (intros; simp [hsVec]; done)
    | (intros; grind)
    | (intros; grind [hsVec])
    | (intros; unfold hsVec; grind)
    | (intros; simp only [hsVec] at * <;> grind)
    | (intros; simp_all [hsVec] <;> grind)
    | (intros; ext <;> grind [hsVec])
    | (intros; constructor <;> intro _ <;> grind [hsVec])
    | (intro x; cases x <;> grind [hsVec])
    | (intro x; induction x <;> simp_all [hsVec])
    | (intro x y; induction x <;> grind [hsVec])
    | (intros; refine ⟨?_, ?_, ?_⟩ <;> intros <;> grind [hsVec])
    | (intros; refine ⟨?_, ?_⟩ <;> intros <;> grind [hsVec])
    | (intros; ext <;> grind)
    | (intros; constructor <;> intro _ <;> grind)
    | (intros; linarith)
    | (intros; tauto)
    | (intros; fun_prop)
    | (intros; simp [*])
    | (intros; solve_by_elim)
  trace "HIT_8_3"



end 
