-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_orth_mem_fullChain_of_mem_49239274c101
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:24:15.157291+00:00
-- url     : https://prove2.me/submissions/51edeb55-45c0-4d36-865a-59ed6e7bb316

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
theorem _root_.solution {𝒲 : IsotropicFlag K H} {W : Submodule E (ι → E)}
    (hW : W ∈ 𝒲.members) : orth K H W ∈ fullChain 𝒲 := by
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
    | (intros; simp [orth, fullChain]; done)
    | (intros; grind)
    | (intros; grind [orth, fullChain])
    | (intros; unfold orth fullChain; grind)
    | (intros; simp only [orth, fullChain] at * <;> grind)
    | (intros; simp_all [orth, fullChain] <;> grind)
    | (intros; ext <;> grind [orth, fullChain])
    | (intros; constructor <;> intro _ <;> grind [orth, fullChain])
    | (intro x; cases x <;> grind [orth, fullChain])
    | (intro x; induction x <;> simp_all [orth, fullChain])
    | (intro x y; induction x <;> grind [orth, fullChain])
    | (intros; refine ⟨?_, ?_, ?_⟩ <;> intros <;> grind [orth, fullChain])
    | (intros; refine ⟨?_, ?_⟩ <;> intros <;> grind [orth, fullChain])
    | (intros; ext <;> grind)
    | (intros; constructor <;> intro _ <;> grind)
    | (intros; linarith)
    | (intros; tauto)
    | (intros; fun_prop)
    | (intros; simp [*])
    | (intros; solve_by_elim)
  trace "HIT_2_3"



end 
