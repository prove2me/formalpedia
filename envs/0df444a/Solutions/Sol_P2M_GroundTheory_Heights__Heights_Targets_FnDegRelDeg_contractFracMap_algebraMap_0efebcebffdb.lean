-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_FnDegRelDeg_contractFracMap_algebraMap_0efebcebffdb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:21:19.395392+00:00
-- url     : https://prove2.me/submissions/fc323425-d570-4ad1-8673-f61d78b7b791

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsFnDegRelDeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PIntNumPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PFnDegRelDeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GroundTheory.Heights₂.Heights.FieldNumbers
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.Targets.FnDegRelDeg
variable {F : Type u} [Field F] {K K' : Type} {ι' : K' → Type} (j : K ↪ K') (P' : Ideal (MRing ι' F))
  [P'.IsPrime] (i' : ∀ k', ι' k')
namespace GroundTheory.Heights₂.Heights.Targets.FnDegRelDeg
theorem _root_.solution (f : MRing (fun k => ι' (j k)) F) :
    contractFracMap j P' (algebraMap _ _ (Ideal.Quotient.mk (contractPrime j P') f)) =
      algebraMap (MRing ι' F ⧸ P') (FractionRing (MRing ι' F ⧸ P'))
        (Ideal.Quotient.mk P' (rename (blockIncl j ι') f)) := by
  simp [contractFracMap, contractQuot]
  rfl
end GroundTheory.Heights₂.Heights.Targets.FnDegRelDeg
