-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FlagTypings_vNumL_perm_1d903d9128b0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:01:43.345114+00:00
-- url     : https://prove2.me/submissions/458d800d-5569-4f67-b5d1-1fc7ed7c9d5a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_TrivBundleIsTwistedForms
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisor
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FlagTypings_intNumL_perm_6fa0b4475d01

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
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {N : ℕ}
omit [Fintype K] [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.FlagTypings
theorem _root_.solution (W : Ideal (MRingOver O ι)) {L₁ L₂ : List (K → ℤ)} (h : L₁.Perm L₂) :
    NumbersDVR.vNumL W L₁ = NumbersDVR.vNumL W L₂ :=
  intNumL_perm (IsLocalRing.ResidueField O) _ h
end GroundTheory.Heights₂.Heights.FlagTypings
