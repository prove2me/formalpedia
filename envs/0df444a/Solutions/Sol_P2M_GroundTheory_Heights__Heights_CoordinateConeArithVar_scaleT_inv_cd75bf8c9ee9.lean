-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CoordinateConeArithVar_scaleT_inv_cd75bf8c9ee9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:52:51.752483+00:00
-- url     : https://prove2.me/submissions/27410d59-89e9-4a5c-af54-085ffb7af143

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_StatementsIntDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PConeTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCoordConeArithVar
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexAt_algebraMap_apply_de37bb391a59


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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.CoordinateConeArithVar
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
omit [Fintype K]
namespace GroundTheory.Heights₂.Heights.CoordinateConeArithVar
theorem _root_.solution (a : K → Ω) (ha : ∀ k, a k ≠ 0) (g : MvPolynomial K Ω) :
    scaleT (fun k ↦ (a k)⁻¹) (scaleT a g) = g := by
  have h : (scaleT (fun k ↦ (a k)⁻¹)).comp (scaleT a) = AlgHom.id Ω _ := by
    refine MvPolynomial.algHom_ext fun k ↦ ?_
    simp only [AlgHom.comp_apply, scaleT, aeval_X, map_mul, aeval_C, AlgHom.id_apply,
      MvPolynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ (ha k), C_1, one_mul]
  exact congrArg (fun φ : MvPolynomial K Ω →ₐ[Ω] MvPolynomial K Ω ↦ φ g) h
end GroundTheory.Heights₂.Heights.CoordinateConeArithVar
