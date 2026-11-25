-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinVariety_liftVar_injective_d44a11af5a3d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:39:45.373159+00:00
-- url     : https://prove2.me/submissions/5838f867-8688-4db3-b7da-f366c56d5e65

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsJoinVariety
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PJoinVariety

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
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx liftVar)
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.JoinVariety
variable {K : Type} {ι : K → Type}
namespace GroundTheory.Heights₂.Heights.NumbersDVR.JoinVariety
theorem _root_.solution : Function.Injective (liftVar (ι := ι) ptIdx) :=
  (varEquiv (ι := ι)).injective.comp (Option.some_injective _)
end GroundTheory.Heights₂.Heights.NumbersDVR.JoinVariety
