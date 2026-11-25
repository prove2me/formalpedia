-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_hasFDerivAt_slice_52338e47dd3d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:32:49.893978+00:00
-- url     : https://prove2.me/submissions/7a62f44c-6718-4120-87a9-b8318a27d831

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceMatricesOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGeneralProjection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceMatricesOpen

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
open Matrix
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {n k : ℕ} {γ : (Fin (k + 1) → ℂ) → Fin n → ℂ} {s : Fin (k + 1) → ℂ}
    (hγ : DifferentiableAt ℂ γ s) (L : Matrix (Fin k) (Fin n) ℂ) :
    HasFDerivAt (fun t => vecCons (t 0) (L *ᵥ γ t)) (sliceDeriv L (fderiv ℂ γ s)) s := by
  have h1 : HasFDerivAt
      (fun t : Fin (k + 1) → ℂ => ((t 0, (Matrix.mulVecLin L).toContinuousLinearMap (γ t)) : ℂ × (Fin k → ℂ)))
      ((ContinuousLinearMap.proj 0).prod ((Matrix.mulVecLin L).toContinuousLinearMap ∘L fderiv ℂ γ s)) s :=
    (hasFDerivAt_apply 0 s).prodMk
      ((Matrix.mulVecLin L).toContinuousLinearMap.hasFDerivAt.comp s hγ.hasFDerivAt)
  exact (Fin.consEquivL ℂ (fun _ : Fin (k + 1) => ℂ)).hasFDerivAt.comp s h1
end GroundTheory.Heights₂.Heights
