-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FlagTypings_isMultiHomog_iff_8163629d7f47
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:05:35.567203+00:00
-- url     : https://prove2.me/submissions/046a02f1-f2de-4752-8ed8-4f766f6d8efd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_TrivBundleIsTwistedForms
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisor
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FlagTypings_weight_blockWeight_8aa7cbb3c809

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FlagTypings
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
set_option linter.unusedSectionVars false
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable {R : Type*} [CommRing R]
namespace GroundTheory.Heights₂.Heights.FlagTypings
theorem _root_.solution (f : MRingOver R ι) (a : K → ℕ) :
    NumbersDVR.IsMultiHomog f a ↔ IsMultiHomog f a := by
  constructor
  · intro h d hd k
    rw [← weight_blockWeight]
    exact congrFun (h (mem_support_iff.mp hd)) k
  · intro h d hd
    funext k
    rw [weight_blockWeight]
    exact h d (mem_support_iff.mpr hd) k
end GroundTheory.Heights₂.Heights.FlagTypings
