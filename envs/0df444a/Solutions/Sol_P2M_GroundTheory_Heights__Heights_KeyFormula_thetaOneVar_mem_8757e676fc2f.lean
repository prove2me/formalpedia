-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KeyFormula_thetaOneVar_mem_8757e676fc2f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:29:38.603635+00:00
-- url     : https://prove2.me/submissions/ae71faea-b36a-482e-a916-e8cef6836beb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ThetaKeyFormula_RigSymFormTauINontrivial
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KeyFormula_jacobiTheta__add_int_cadb2154e0f2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KeyFormula_jacobiTheta__add_int_mul_6ed98b2144e6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KeyFormula_intVec_one_081da4c52f7a

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.KeyFormula
open Complex Matrix Real
noncomputable section
namespace GroundTheory.Heights₂.Heights.KeyFormula
theorem _root_.solution : thetaOneVar ∈ thetaSec tauI (HalfChar.zero 1) 1 := by
  refine ⟨?_, fun v z => ?_, fun u z => ?_⟩
  · intro z
    have h1 : DifferentiableAt ℂ (fun w : ℂ => jacobiTheta₂ w I) (z 0) :=
      differentiableAt_jacobiTheta₂_fst (z 0) (by simp)
    have h2 : DifferentiableAt ℂ (fun z : Fin 1 → ℂ => z 0) z := (differentiable_apply 0) z
    exact h1.comp z h2
  · have : perFactor (HalfChar.zero 1) 1 v = 1 := by
      simp [perFactor, HalfChar.a, HalfChar.zero, dotProduct]
    rw [this, one_mul]
    simp only [thetaOneVar, Pi.add_apply, intVec_one]
    exact jacobiTheta₂_add_int (z 0) I (v 0)
  · simp only [thetaOneVar, Pi.add_apply, autFactor, tauI]
    have hτ : ((I • (1 : Matrix (Fin 1) (Fin 1) ℂ)) *ᵥ intVec u) 0 = (u 0 : ℂ) * I := by
      simp [Matrix.mulVec, dotProduct, intVec, mul_comm]
    rw [hτ, jacobiTheta₂_add_int_mul]
    congr 2
    simp [dotProduct, Matrix.mulVec, intVec, HalfChar.b, HalfChar.zero]
    ring
end GroundTheory.Heights₂.Heights.KeyFormula
