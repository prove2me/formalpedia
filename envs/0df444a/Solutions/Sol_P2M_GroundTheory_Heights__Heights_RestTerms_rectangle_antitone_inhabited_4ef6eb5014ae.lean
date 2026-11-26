-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_rectangle_antitone_inhabited_4ef6eb5014ae
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:06:16.374801+00:00
-- url     : https://prove2.me/submissions/a856cd1a-293d-4a31-b6dd-ae35a2885e88

import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset
noncomputable section
theorem _root_.solution : Antitone (rectangle 2 3) := by
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
    | (intros; simp [rectangle]; done)
    | (intros; grind)
    | (intros; grind [rectangle])
    | (intros; unfold rectangle; grind)
    | (intros; simp only [rectangle] at * <;> grind)
    | (intros; simp_all [rectangle] <;> grind)
    | (intros; ext <;> grind [rectangle])
    | (intros; constructor <;> intro _ <;> grind [rectangle])
    | (intro x; cases x <;> grind [rectangle])
    | (intro x; induction x <;> simp_all [rectangle])
    | (intro x y; induction x <;> grind [rectangle])
    | (intros; refine ⟨?_, ?_, ?_⟩ <;> intros <;> grind [rectangle])
    | (intros; refine ⟨?_, ?_⟩ <;> intros <;> grind [rectangle])
    | (intros; ext <;> grind)
    | (intros; constructor <;> intro _ <;> grind)
    | (intros; linarith)
    | (intros; tauto)
    | (intros; fun_prop)
    | (intros; simp [*])
    | (intros; solve_by_elim)
  trace "HIT_47_0"



end 
