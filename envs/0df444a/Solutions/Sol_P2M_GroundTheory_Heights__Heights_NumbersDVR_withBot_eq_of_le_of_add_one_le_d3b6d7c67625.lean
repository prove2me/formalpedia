-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_withBot_eq_of_le_of_add_one_le_d3b6d7c67625
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:44:52.996915+00:00
-- url     : https://prove2.me/submissions/2f0a2e07-34c3-4ac2-a081-0eb28cd6e4f9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsComponentDim
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CycDim
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppAB
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_WithBotEqOfLeOfAddOneLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PComponentDim
import Theorems.Thm_UpperTheory_Reformulated_B_Ydd3_withBot_eq_of_le_of_add_one_le


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
theorem _root_.solution {x : WithBot ℕ∞} {c : ℕ} (h1 : (c : WithBot ℕ∞) ≤ x)
    (h2 : x + 1 ≤ ((c + 1 : ℕ) : WithBot ℕ∞)) : x = c :=
  _root_.UpperTheory.Reformulated.B.Ydd3.withBot_eq_of_le_of_add_one_le h1 h2
end GroundTheory.Heights₂.Heights.NumbersDVR
