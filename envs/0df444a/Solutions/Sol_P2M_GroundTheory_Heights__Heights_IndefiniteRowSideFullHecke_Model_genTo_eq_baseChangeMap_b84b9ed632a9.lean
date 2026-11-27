-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_genTo_eq_baseChangeMap_b84b9ed632a9
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:22:29.510944+00:00
-- url     : https://prove2.me/submissions/72e53a1f-0c4c-405a-b377-f216d55e9d92

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
theorem _root_.solution (X : Scheme.{0}) :
    genTo X = GroundTheory.Heights₂.Heights.Model.baseChangeMap (toSpecZ X) ℚ := by
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
    | (intros; simp [baseChangeMap, toSpecZ, genTo]; done)
    | (intros; grind)
    | (intros; grind [baseChangeMap, toSpecZ, genTo])
    | (intros; unfold baseChangeMap toSpecZ genTo; grind)
    | (intros; simp only [baseChangeMap, toSpecZ, genTo] at * <;> grind)
    | (intros; simp_all [baseChangeMap, toSpecZ, genTo] <;> grind)
    | (intros; ext <;> grind [baseChangeMap, toSpecZ, genTo])
    | (intros; constructor <;> intro _ <;> grind [baseChangeMap, toSpecZ, genTo])
    | (intro x; cases x <;> grind [baseChangeMap, toSpecZ, genTo])
    | (intro x; induction x <;> simp_all [baseChangeMap, toSpecZ, genTo])
    | (intro x y; induction x <;> grind [baseChangeMap, toSpecZ, genTo])
    | (intros; refine ⟨?_, ?_, ?_⟩ <;> intros <;> grind [baseChangeMap, toSpecZ, genTo])
    | (intros; refine ⟨?_, ?_⟩ <;> intros <;> grind [baseChangeMap, toSpecZ, genTo])
    | (intros; ext <;> grind)
    | (intros; constructor <;> intro _ <;> grind)
    | (intros; linarith)
    | (intros; tauto)
    | (intros; fun_prop)
    | (intros; simp [*])
    | (intros; solve_by_elim)
  trace "HIT_16_0"



end 
