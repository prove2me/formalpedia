-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_pullDeg_add_22e9381938f4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:59:19.390829+00:00
-- url     : https://prove2.me/submissions/4c6709c5-6f39-4110-bb65-0ac6a39e602f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsFurtherTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsMultiHomogFirstCoordinate
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_TableDegreeThreeBase

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
  {K' : Type*} [Fintype K'] {ι' : K' → Type*} [∀ k, Fintype (ι' k)]
omit [Fintype K] [Fintype K']
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution (κ : K → K') (a b : K → ℤ) : pullDeg κ (a + b) = pullDeg κ a + pullDeg κ b := by
  classical
  funext k'
  simp only [pullDeg, Function.extend, Pi.add_apply]
  split_ifs <;> simp
end GroundTheory.Heights₂.Heights.Inter
