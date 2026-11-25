-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_FnDegRelDeg_contractFracMap_comp_dehom_643f296b3106
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:29:26.869507+00:00
-- url     : https://prove2.me/submissions/a9cabadd-6fcf-4b0b-92fb-bc594dc6c788

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsFnDegRelDeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PIntNumPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PFnDegRelDeg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_FnDegRelDeg_contractFracMap_algebraMap_0efebcebffdb

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
theorem _root_.solution :
    (contractFracMap j P').comp (IntNumPoint.dehom (contractPrime j P') (fun k => i' (j k))) =
      (IntNumPoint.dehom P' i').comp (rename (blockIncl j ι')) := by
  refine MvPolynomial.algHom_ext fun r => ?_
  simp only [AlgHom.comp_apply, IntNumPoint.dehom, aeval_X, rename_X, map_div₀, IntNumPoint.xc,
    contractFracMap_algebraMap]
  rfl
end GroundTheory.Heights₂.Heights.Targets.FnDegRelDeg
