-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_rename_closureForm_d4ffbeabd6a1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:15:24.660651+00:00
-- url     : https://prove2.me/submissions/045226c8-63ec-4b9a-ad4b-d782b1c380cc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSegreFlagClosure
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagIndependence
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsPairNumberRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsVerticalDivisorJoinPullback
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSegreFlagClosureBirational
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagIndependenceAlgebra
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSegreFlagClosurePullback
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_rename_liftPairForm_b37bf41d9bb8

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
variable {K : Type} {ι : K → Type} {m : ℕ}
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {R : Type*} [CommRing R] (M M' : ℕ) (h : MRing (bundleIdx (bundleIdx ι M) M') R)
    (F : Fin m → MRing ι R) :
    (fun i => rename (closureVarEquiv ι M M') (closureForm M M' h F i)) =
      joinClosureForm M M' (rename (closureVarEquiv ι M M') h) F := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · simp only [joinClosureForm, closureForm, Fin.append_left]
  · simp only [joinClosureForm, closureForm, Fin.append_right]
    exact rename_liftPairForm ι M M' _
end GroundTheory.Heights₂.Heights.NumbersDVR
