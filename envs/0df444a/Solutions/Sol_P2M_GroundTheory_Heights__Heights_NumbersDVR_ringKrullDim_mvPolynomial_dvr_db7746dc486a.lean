-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_ringKrullDim_mvPolynomial_dvr_db7746dc486a
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:45:45.065798+00:00
-- url     : https://prove2.me/submissions/ff8e4611-ce2a-4e1a-8333-5c3984dc4471

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsComponentDim
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CycDim
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppAB
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_WithBotEqOfLeOfAddOneLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PComponentDim

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
universe u
variable {σ : Type*} [Finite σ]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution (O : Type*) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] :
    ringKrullDim (MvPolynomial σ O) = ((Nat.card σ + 1 : ℕ) : WithBot ℕ∞) := by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, IsDiscreteValuationRing.ringKrullDim_eq_one]
  push_cast
  ring
end GroundTheory.Heights₂.Heights.NumbersDVR
