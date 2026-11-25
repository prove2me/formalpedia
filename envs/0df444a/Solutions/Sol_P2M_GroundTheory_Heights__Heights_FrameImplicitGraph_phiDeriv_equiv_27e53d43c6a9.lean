-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FrameImplicitGraph_phiDeriv_equiv_27e53d43c6a9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:42:18.860303+00:00
-- url     : https://prove2.me/submissions/d02cda61-d55c-4de6-b630-1266fb77d5e9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StFrameImplicitGraph
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_HasStrictFDerivAtEval
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PFrameImplicitGraph
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FrameImplicitGraph_phiDeriv_injective_25c5f20f89f1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FrameImplicitGraph_finrank_eq_59867f7e7a5b

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
noncomputable section
open MvPolynomial
open GroundTheory.Heights₂.Heights.FrameImplicitGraph
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.FrameImplicitGraph
theorem _root_.solution (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (I : Finset (Fin n)) (f : {j // j ∉ I} → MvPolynomial (Fin n) ℂ) (x : EuclideanSpace ℂ (Fin n))
    (hx : eval (fun i => x i) (frameJacobianDet b I f) ≠ 0) :
    ∃ e : EuclideanSpace ℂ (Fin n) ≃L[ℂ] (I → ℂ) × ({j // j ∉ I} → ℂ),
      (e : EuclideanSpace ℂ (Fin n) →L[ℂ] (I → ℂ) × ({j // j ∉ I} → ℂ)) = phiDeriv b I f x := by
  refine ⟨(LinearMap.linearEquivOfInjective (phiDeriv b I f x : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] _)
    (phiDeriv_injective b I f x hx) (finrank_eq I)).toContinuousLinearEquiv, ?_⟩
  ext v
  all_goals simp [LinearMap.linearEquivOfInjective_apply]
end GroundTheory.Heights₂.Heights.FrameImplicitGraph
