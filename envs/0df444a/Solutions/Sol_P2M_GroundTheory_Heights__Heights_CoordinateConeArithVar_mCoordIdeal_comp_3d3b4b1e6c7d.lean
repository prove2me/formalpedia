-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CoordinateConeArithVar_mCoordIdeal_comp_3d3b4b1e6c7d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:52:46.112806+00:00
-- url     : https://prove2.me/submissions/a5713194-bcaf-436a-80f0-f7febe030c58

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_StatementsIntDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PConeTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCoordConeArithVar

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
theorem _root_.solution {L : Type} [Field L] (σ : L →+* Ω) (z : (Σ k, ι k) → L) :
    mCoordIdeal (fun p ↦ σ (z p)) = mCoordIdeal z := by
  have h : ∀ f, mConeMap (fun p ↦ σ (z p)) f = MvPolynomial.map σ (mConeMap z f) := by
    have e : (mConeMap (fun p ↦ σ (z p)) : MRing ι →+* MvPolynomial K Ω) =
        (MvPolynomial.map σ).comp (mConeMap z : MRing ι →+* MvPolynomial K L) := by
      refine MvPolynomial.ringHom_ext (fun a ↦ ?_) (fun p ↦ ?_) <;> simp [mConeMap]
    exact fun f ↦ RingHom.congr_fun e f
  ext f
  simp only [mCoordIdeal, RingHom.mem_ker, h]
  exact map_eq_zero_iff _ (MvPolynomial.map_injective σ σ.injective)
end GroundTheory.Heights₂.Heights.CoordinateConeArithVar
