-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_isVectorBundle_iff_model_7c6200fe56e7
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:22:30.955849+00:00
-- url     : https://prove2.me/submissions/3730cd10-9e83-4b7c-95ec-b0e55005236a

import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_IsIsoPullbackObjUnitToUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_IsVectorBundleIffModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
open CategoryTheory Opposite AlgebraicGeometry Limits
noncomputable section
theorem _root_.solution {X : Scheme.{0}} (E : X.Modules) :
    GroundTheory.Heights₂.Heights.Model.IsVectorBundle E ↔ IsVectorBundle E := by
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
    | (intros; simp [IsVectorBundle]; done)
    | (intros; grind)
    | (intros; grind [IsVectorBundle])
    | (intros; unfold IsVectorBundle; grind)
    | (intros; simp only [IsVectorBundle] at * <;> grind)
    | (intros; simp_all [IsVectorBundle] <;> grind)
    | (intros; ext <;> grind [IsVectorBundle])
    | (intros; constructor <;> intro _ <;> grind [IsVectorBundle])
    | (intro x; cases x <;> grind [IsVectorBundle])
    | (intro x; induction x <;> simp_all [IsVectorBundle])
    | (intro x y; induction x <;> grind [IsVectorBundle])
    | (intros; refine ⟨?_, ?_, ?_⟩ <;> intros <;> grind [IsVectorBundle])
    | (intros; refine ⟨?_, ?_⟩ <;> intros <;> grind [IsVectorBundle])
    | (intros; ext <;> grind)
    | (intros; constructor <;> intro _ <;> grind)
    | (intros; linarith)
    | (intros; tauto)
    | (intros; fun_prop)
    | (intros; simp [*])
    | (intros; solve_by_elim)
  trace "HIT_16_2"



end 
