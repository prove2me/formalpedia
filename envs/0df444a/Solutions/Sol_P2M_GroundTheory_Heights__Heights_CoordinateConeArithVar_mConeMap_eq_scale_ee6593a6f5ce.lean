-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CoordinateConeArithVar_mConeMap_eq_scale_ee6593a6f5ce
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:52:41.710804+00:00
-- url     : https://prove2.me/submissions/ced2cfbc-5b84-4524-9324-73b6097322ad

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
omit [Fintype K] [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.CoordinateConeArithVar
theorem _root_.solution (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    (f : MRing ι) :
    mConeMap y f = scaleT (fun k ↦ y ⟨k, c k⟩) (mConeMap (ratioPt y c) f) := by
  have h : (mConeMap y : MRing ι →+* MvPolynomial K Ω) =
      (scaleT fun k ↦ y ⟨k, c k⟩ : MvPolynomial K Ω →+* MvPolynomial K Ω).comp
        (mConeMap (ratioPt y c) : MRing ι →+* MvPolynomial K Ω) := by
    refine MvPolynomial.ringHom_ext (fun a ↦ ?_) (fun p ↦ ?_)
    · simp [mConeMap, scaleT]
    · simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, mConeMap, aeval_X, scaleT,
        map_mul, aeval_C, MvPolynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
        ratioPt]
      rw [← mul_assoc, ← C_mul, div_mul_cancel₀ _ (hc p.1)]
  exact RingHom.congr_fun h f
end GroundTheory.Heights₂.Heights.CoordinateConeArithVar
