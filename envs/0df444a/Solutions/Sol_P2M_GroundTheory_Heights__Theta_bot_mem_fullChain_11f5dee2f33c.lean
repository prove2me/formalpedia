-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_bot_mem_fullChain_11f5dee2f33c
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:24:14.531527+00:00
-- url     : https://prove2.me/submissions/d6be3d02-4720-40f5-86a6-927541d92569

import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_Parabolic
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
open Module Matrix TensorProduct GroundTheory.Automorphic NumberField
open scoped NumberField.AdeleRing
noncomputable section
set_option linter.unusedSectionVars false
open scoped Classical
variable {K E : Type*} [Field K] [Field E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (K) (H : Matrix ι ι E)
variable {K H}
theorem _root_.solution (𝒲 : IsotropicFlag K H) : ⊥ ∈ fullChain 𝒲 := by
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
    | (intros; simp [fullChain]; done)
    | (intros; grind)
    | (intros; grind [fullChain])
    | (intros; unfold fullChain; grind)
    | (intros; simp only [fullChain] at * <;> grind)
    | (intros; simp_all [fullChain] <;> grind)
    | (intros; ext <;> grind [fullChain])
    | (intros; constructor <;> intro _ <;> grind [fullChain])
    | (intro x; cases x <;> grind [fullChain])
    | (intro x; induction x <;> simp_all [fullChain])
    | (intro x y; induction x <;> grind [fullChain])
    | (intros; refine ⟨?_, ?_, ?_⟩ <;> intros <;> grind [fullChain])
    | (intros; refine ⟨?_, ?_⟩ <;> intros <;> grind [fullChain])
    | (intros; ext <;> grind)
    | (intros; constructor <;> intro _ <;> grind)
    | (intros; linarith)
    | (intros; tauto)
    | (intros; fun_prop)
    | (intros; simp [*])
    | (intros; solve_by_elim)
  trace "HIT_2_2"



end 
