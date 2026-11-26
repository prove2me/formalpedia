-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_mem_invOpen_id_611cc6ee4669
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:08:48.120871+00:00
-- url     : https://prove2.me/submissions/e998b970-c1d0-48cc-abce-4eb6b9c6ec6a

import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsGlue
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
theorem _root_.solution (m : ℤ) (x : SpecZ) : x ∈ invOpen (𝟙 SpecZ) m ↔ m ∉ x.asIdeal := by
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
    | (intros; simp [SpecZ, invOpen]; done)
    | (intros; grind)
    | (intros; grind [SpecZ, invOpen])
    | (intros; unfold SpecZ invOpen; grind)
    | (intros; simp only [SpecZ, invOpen] at * <;> grind)
    | (intros; simp_all [SpecZ, invOpen] <;> grind)
    | (intros; ext <;> grind [SpecZ, invOpen])
    | (intros; constructor <;> intro _ <;> grind [SpecZ, invOpen])
    | (intro x; cases x <;> grind [SpecZ, invOpen])
    | (intro x; induction x <;> simp_all [SpecZ, invOpen])
    | (intro x y; induction x <;> grind [SpecZ, invOpen])
    | (intros; refine ⟨?_, ?_, ?_⟩ <;> intros <;> grind [SpecZ, invOpen])
    | (intros; refine ⟨?_, ?_⟩ <;> intros <;> grind [SpecZ, invOpen])
    | (intros; ext <;> grind)
    | (intros; constructor <;> intro _ <;> grind)
    | (intros; linarith)
    | (intros; tauto)
    | (intros; fun_prop)
    | (intros; simp [*])
    | (intros; solve_by_elim)
  trace "HIT_27_0"



end 
