-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_isFlagPair_self_349f1f6d80b2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:07:39.168215+00:00
-- url     : https://prove2.me/submissions/31b03373-c76b-4600-9fb3-a6ef99408830

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBundles
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_isVerticalDivisor_one_177da7b5f629
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_isFlagFrame_scaledTriv_9910a8ec665d


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
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} {Ω : Type*} [Field Ω]
  {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution (ϖ : O) (y : (Σ k, ι k) → Ω) (r : ℕ) {s : Ω} (hs : s ≠ 0) :
    IsFlagPair ϖ y (scaledTrivBundle O (segreVec y) r hs) (scaledTrivBundle O (segreVec y) r hs)
      (scaledBasis r hs) (scaledBasis r hs) 0 0 (fun _ => 1) (fun _ => 1) where
  flag := isFlagFrame_scaledTriv O y r hs
  flag' := isFlagFrame_scaledTriv O y r hs
  sameFlag i j hij := by
    simp [Module.Basis.repr_self, ne_of_lt hij]
  vertical i := by
    have h0 : ((0 : Fin r → K → ℤ) i - (0 : Fin r → K → ℤ) i) = 0 := sub_self _
    rw [h0]
    exact isVerticalDivisor_one ϖ _
  generic i := by
    simp
end GroundTheory.Heights₂.Heights.NumbersDVR
