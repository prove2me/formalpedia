-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AddBlockBridge_scale_injective_d67dd2591a0b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:34:18.801247+00:00
-- url     : https://prove2.me/submissions/70920200-684c-4840-b1c1-2ce494853563

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PAddHeightsridge

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace AddBlockBridge
theorem _root_.solution {σ L : Type} [Field L] (w : σ → L) (hw : ∀ o, w o ≠ 0) :
    Function.Injective (aeval fun o ↦ C (w o) * X o : MvPolynomial σ L →ₐ[L] MvPolynomial σ L) := by
  have h : ((aeval fun o ↦ C (w o)⁻¹ * X o : MvPolynomial σ L →ₐ[L] MvPolynomial σ L).comp
      (aeval fun o ↦ C (w o) * X o)) = AlgHom.id L _ := by
    refine algHom_ext fun o ↦ ?_
    simp only [AlgHom.comp_apply, aeval_X, map_mul, aeval_C, algebraMap_eq, AlgHom.id_apply]
    rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ (hw o), C_1, one_mul]
  exact Function.LeftInverse.injective (g := aeval fun o ↦ C (w o)⁻¹ * X o) fun p ↦ by
    simpa using congrArg (fun φ ↦ φ p) h
end AddBlockBridge
end GroundTheory.Heights₂.Heights
