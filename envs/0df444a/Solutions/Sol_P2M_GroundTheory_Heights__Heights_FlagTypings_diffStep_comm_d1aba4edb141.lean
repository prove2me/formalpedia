-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FlagTypings_diffStep_comm_d1aba4edb141
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:27:12.784659+00:00
-- url     : https://prove2.me/submissions/b1d8b86b-f9c9-4e33-8a79-5d8f84d5598e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_TrivBundleIsTwistedForms
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisor

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
omit [Fintype K] [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.FlagTypings
theorem _root_.solution (a b : K → ℤ) (h : (K → ℤ) → ℤ) :
    NumbersDVR.diffStep a (NumbersDVR.diffStep b h) =
      NumbersDVR.diffStep b (NumbersDVR.diffStep a h) := by
  funext m
  simp only [NumbersDVR.diffStep]
  rw [sub_right_comm m a b]
  ring
end GroundTheory.Heights₂.Heights.FlagTypings
