-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_pbSection_eq_pullSection_586a7923eab1
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:22:30.352789+00:00
-- url     : https://prove2.me/submissions/839edbfd-0efe-4d91-87ac-e6d985b43a0d

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
theorem _root_.solution {A B : Scheme.{0}} (f : A ⟶ B) (M : B.Modules) (t : Γ(M, ⊤)) :
    pbSection f M t = GroundTheory.Heights₂.Heights.Model.pullSection f M t := by
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
    | (intros; simp [pullSection, pbSection]; done)
    | (intros; grind)
    | (intros; grind [pullSection, pbSection])
    | (intros; unfold pullSection pbSection; grind)
    | (intros; simp only [pullSection, pbSection] at * <;> grind)
    | (intros; simp_all [pullSection, pbSection] <;> grind)
    | (intros; ext <;> grind [pullSection, pbSection])
    | (intros; constructor <;> intro _ <;> grind [pullSection, pbSection])
    | (intro x; cases x <;> grind [pullSection, pbSection])
    | (intro x; induction x <;> simp_all [pullSection, pbSection])
    | (intro x y; induction x <;> grind [pullSection, pbSection])
    | (intros; refine ⟨?_, ?_, ?_⟩ <;> intros <;> grind [pullSection, pbSection])
    | (intros; refine ⟨?_, ?_⟩ <;> intros <;> grind [pullSection, pbSection])
    | (intros; ext <;> grind)
    | (intros; constructor <;> intro _ <;> grind)
    | (intros; linarith)
    | (intros; tauto)
    | (intros; fun_prop)
    | (intros; simp [*])
    | (intros; solve_by_elim)
  trace "HIT_16_1"



end 
