-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinPointVerticalDivisor_rename_mem_mcIdeal_iff_d436a9d64f9d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:15:18.303167+00:00
-- url     : https://prove2.me/submissions/1420c21b-b9db-4fce-a23b-75c1bb3a8a5f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsTerExtra
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PVerticalDivisorJoinPullback
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisorAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ClassListMapDomainPerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinJoinPointVertDiv
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_joinCoords_eq_eddac3903903
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_joinForm_eq_ec92fe149fc0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_joinForm_mem_pointIdeal_iff_ec545b5ede48


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
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx ptCoord liftVar pullDeg joinCoord mcIdeal IsVertDiv)
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.JoinPointVerticalDivisor
variable {K K' : Type} [Fintype K] [Fintype K'] {ι : K → Type} {ι' : K' → Type}
variable [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.JoinPointVerticalDivisor
theorem _root_.solution (R : Type) [CommRing R] {Ω : Type} [Field Ω] [Algebra R Ω]
    (y : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω) (h : MvPolynomial (Σ k, ι k) R) :
    rename (liftVar ι') h ∈ mcIdeal R (joinCoord y z) ↔ h ∈ mcIdeal R y := by
  rw [← BundleExamples.joinCoords_eq, ← BundleExamples.joinForm_eq]
  exact joinForm_mem_pointIdeal_iff R y z h
end GroundTheory.Heights₂.Heights.NumbersDVR.JoinPointVerticalDivisor
