-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FlagTypings_divCycle_eq_4ff6952c8612
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:27:13.616128+00:00
-- url     : https://prove2.me/submissions/6ced1a18-7b8b-4de1-98ed-541b9585e8b8

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
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.FlagTypings
theorem _root_.solution {R : Type*} [CommRing R] [IsNoetherianRing R] (P : Ideal (MRingOver R ι))
    (f : MRingOver R ι) (W : Ideal (MRingOver R ι)) :
    NumbersDVR.divCycle P f W = (ReciprocityTheory.ChartRestriction.G.Geo.divCycle P f W : ℤ) := by
  classical
  have hL : (ReciprocityTheory.ChartRestriction.G.Geo.divCycle P f W : ℕ) =
      if W ∈ divSupp P f then multAt (P ⊔ Ideal.span {f}) W else 0 := rfl
  rw [NumbersDVR.divCycle, hL]
  by_cases h : W ∈ (P ⊔ Ideal.span {f}).minimalPrimes ∧ NumbersDVR.IsRelevant W
  · have h' : W ∈ divSupp P f := h
    rw [dif_pos h, if_pos h', multAt, dif_pos h.1.1.1]
    rfl
  · have h' : W ∉ divSupp P f := h
    rw [dif_neg h, if_neg h']
    simp
end GroundTheory.Heights₂.Heights.FlagTypings
