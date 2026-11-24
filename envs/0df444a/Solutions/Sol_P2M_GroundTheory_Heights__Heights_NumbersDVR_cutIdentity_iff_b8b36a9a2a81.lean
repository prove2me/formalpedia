-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_cutIdentity_iff_b8b36a9a2a81
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:40:14.194084+00:00
-- url     : https://prove2.me/submissions/752a210e-e2d5-4e6b-8e2e-1b90081a305f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_SpanTwoIsPrimeRelevant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_CutIdentityRightSideCongrOfSubMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
universe u
variable {K : Type*} [DecidableEq K] {ι : K → Type*}
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution (ϖ : O) (P : Ideal (MRing ι O)) (b : K → ℤ) (f g : MRing ι O) (c : K → ℕ)
    (s : MRing ι O) {d : ℕ} (L : Fin d → K → ℤ) :
    cutIdentity ϖ P b f g c s L ↔ cutIdentityLeftSide P f g c L = cutIdentityRightSide ϖ P b f g s L :=
  Iff.rfl
end GroundTheory.Heights₂.Heights.NumbersDVR
