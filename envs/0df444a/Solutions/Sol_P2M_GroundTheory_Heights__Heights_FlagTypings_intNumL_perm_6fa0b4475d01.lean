-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FlagTypings_intNumL_perm_6fa0b4475d01
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:05:00.737201+00:00
-- url     : https://prove2.me/submissions/03d5d00c-71c5-46b6-9787-e14cf295128a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_TrivBundleIsTwistedForms
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisor
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FlagTypings_diffStep_comm_d1aba4edb141

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
theorem _root_.solution (F : Type*) [Field F] (V : Ideal (MRingOver F ι)) {L₁ L₂ : List (K → ℤ)}
    (h : L₁.Perm L₂) : NumbersDVR.intNumL F V L₁ = NumbersDVR.intNumL F V L₂ := by
  have : LeftCommutative (NumbersDVR.diffStep (K := K)) := ⟨diffStep_comm⟩
  simp only [NumbersDVR.intNumL, NumbersDVR.intNum, NumbersDVR.mixedDiff, List.ofFn_get]
  rw [h.foldr_eq]
end GroundTheory.Heights₂.Heights.FlagTypings
