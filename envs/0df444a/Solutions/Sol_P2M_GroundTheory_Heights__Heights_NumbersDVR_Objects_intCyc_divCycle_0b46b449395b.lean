-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_Objects_intCyc_divCycle_0b46b449395b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:43.405803+00:00
-- url     : https://prove2.me/submissions/f65160a9-438a-4fe7-8320-5f490319f559

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_MemOfMemSupportDivCycle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisorAlt

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
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.Objects
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable {R : Type*} [CommRing R]
attribute [local instance] MvPolynomial.weightedGradedAlgebra
omit [DecidableEq K]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.Objects
theorem _root_.solution [IsNoetherianRing R] (P : Ideal (MRing ι R)) (s : MRing ι R)
    (W : Ideal (MRing ι R)) :
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.intCyc (ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s) W =
      divCycle P s W := by
  classical
  have hc : (ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s : Ideal (MRing ι R) → ℕ) W =
      if W ∈ ReciprocityTheory.ChartRestriction.G.Geo.divSupp P s then
        ReciprocityTheory.ChartRestriction.G.Geo.multAt (P ⊔ Ideal.span {s}) W else 0 := by
    unfold ReciprocityTheory.ChartRestriction.G.Geo.divCycle
    rw [Finsupp.ofSupportFinite_coe]
  rw [GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.intCyc, Finsupp.mapRange_apply, hc, divCycle]
  by_cases h : W ∈ (P ⊔ Ideal.span {s}).minimalPrimes ∧ IsRelevant W
  · have h' : W ∈ ReciprocityTheory.ChartRestriction.G.Geo.divSupp P s := h
    rw [if_pos h', dif_pos h, ReciprocityTheory.ChartRestriction.G.Geo.multAt, dif_pos h.1.1.1]
    all_goals rfl
  · have h' : W ∉ ReciprocityTheory.ChartRestriction.G.Geo.divSupp P s := h
    rw [if_neg h', dif_neg h, Nat.cast_zero]
end GroundTheory.Heights₂.Heights.NumbersDVR.Objects
