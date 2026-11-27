-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_mem_unipotentRadical_38b14c233376
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:24:13.819941+00:00
-- url     : https://prove2.me/submissions/bbb5d26d-e2d0-479f-b993-57746e95438e

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
variable (H : Matrix ι ι E)
variable (R : Type*) [CommRing R] [Algebra K R]
variable {H R}
theorem _root_.solution {𝒲 : IsotropicFlag K H} {g : unitaryPoints K E H R} :
    g ∈ unipotentRadical H R 𝒲 ↔ ∀ B ∈ fullChain 𝒲, ∀ x ∈ extendScalars K R B,
      unitaryMat g *ᵥ x - x ∈ extendScalars K R (below (fullChain 𝒲) B) ∧
      unitaryMat g⁻¹ *ᵥ x - x ∈ extendScalars K R (below (fullChain 𝒲) B) := by
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
    | (intros; simp [fullChain, below, extendScalars, unipotentRadical]; done)
    | (intros; grind)
    | (intros; grind [fullChain, below, extendScalars, unipotentRadical])
    | (intros; unfold fullChain below extendScalars unipotentRadical; grind)
    | (intros; simp only [fullChain, below, extendScalars, unipotentRadical] at * <;> grind)
    | (intros; simp_all [fullChain, below, extendScalars, unipotentRadical] <;> grind)
    | (intros; ext <;> grind [fullChain, below, extendScalars, unipotentRadical])
    | (intros; constructor <;> intro _ <;> grind [fullChain, below, extendScalars, unipotentRadical])
    | (intro x; cases x <;> grind [fullChain, below, extendScalars, unipotentRadical])
    | (intro x; induction x <;> simp_all [fullChain, below, extendScalars, unipotentRadical])
    | (intro x y; induction x <;> grind [fullChain, below, extendScalars, unipotentRadical])
    | (intros; refine ⟨?_, ?_, ?_⟩ <;> intros <;> grind [fullChain, below, extendScalars, unipotentRadical])
    | (intros; refine ⟨?_, ?_⟩ <;> intros <;> grind [fullChain, below, extendScalars, unipotentRadical])
    | (intros; ext <;> grind)
    | (intros; constructor <;> intro _ <;> grind)
    | (intros; linarith)
    | (intros; tauto)
    | (intros; fun_prop)
    | (intros; simp [*])
    | (intros; solve_by_elim)
  trace "HIT_2_0"



end 
