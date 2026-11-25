-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_RegularityValuationCentre_ltIdeal_one_isPrime_d8f39af7a16f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:03:20.853687+00:00
-- url     : https://prove2.me/submissions/a51792bd-87f8-4f2b-86fc-b96b3e278dcc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ExistsIntValuationLtOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_KerIsMultiHomogIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
attribute [local instance] MvPolynomial.weightedGradedAlgebra
open GroundTheory.Heights₂.Heights.Inter.RegularityValuationCentre
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter.RegularityValuationCentre
theorem _root_.solution {R Γ : Type*} [CommRing R] [LinearOrderedCommGroupWithZero Γ] (v : Valuation R Γ) :
    (v.ltIdeal 1).IsPrime := by
  refine ⟨fun h => ?_, fun {x y} hxy => ?_⟩
  · have h1 : (1 : v.integer) ∈ v.ltIdeal 1 := h ▸ Submodule.mem_top
    simp [Valuation.mem_ltIdeal_iff] at h1
  · simp only [Valuation.mem_ltIdeal_iff, Units.val_one] at hxy ⊢
    by_contra hc
    push Not at hc
    have hx : v x = 1 := le_antisymm x.2 hc.1
    have hy : v y = 1 := le_antisymm y.2 hc.2
    simp [Subring.coe_mul, map_mul, hx, hy] at hxy
end GroundTheory.Heights₂.Heights.Inter.RegularityValuationCentre
