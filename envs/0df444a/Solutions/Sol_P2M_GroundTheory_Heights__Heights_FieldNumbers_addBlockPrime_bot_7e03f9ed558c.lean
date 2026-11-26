-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_addBlockPrime_bot_7e03f9ed558c
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:08:11.95695+00:00
-- url     : https://prove2.me/submissions/46da7b42-9b9e-4ee5-82fd-7db728a25acb

import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsExamples
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
theorem _root_.solution {K : Type*} {F : Type*} [Field F] (ι : K → Type) (N : ℕ) :
    addBlockPrime N (⊥ : Ideal (MRing ι F)) = ⊥ := by
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
    | (intros; simp [addBlockPrime]; done)
    | (intros; grind)
    | (intros; grind [addBlockPrime])
    | (intros; unfold addBlockPrime; grind)
    | (intros; simp only [addBlockPrime] at * <;> grind)
    | (intros; simp_all [addBlockPrime] <;> grind)
    | (intros; ext <;> grind [addBlockPrime])
    | (intros; constructor <;> intro _ <;> grind [addBlockPrime])
    | (intro x; cases x <;> grind [addBlockPrime])
    | (intro x; induction x <;> simp_all [addBlockPrime])
    | (intro x y; induction x <;> grind [addBlockPrime])
    | (intros; refine ⟨?_, ?_, ?_⟩ <;> intros <;> grind [addBlockPrime])
    | (intros; refine ⟨?_, ?_⟩ <;> intros <;> grind [addBlockPrime])
    | (intros; ext <;> grind)
    | (intros; constructor <;> intro _ <;> grind)
    | (intros; linarith)
    | (intros; tauto)
    | (intros; fun_prop)
    | (intros; simp [*])
    | (intros; solve_by_elim)
  trace "HIT_9_1"



end 
