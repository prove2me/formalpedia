-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_SwapCyclesAlt_divCycle_of_not_mem_e510c3578bb2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:56:48.640436+00:00
-- url     : https://prove2.me/submissions/4a24f8ec-6103-4cce-b1bc-ca31c25634f8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSwapCyclesArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSwap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_NotRelevantOfDimZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemMinimalPrimesOfMemDivSuppDivSupp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSwapCycles

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1
  ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.SwapCyclesAlt
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter.SwapCyclesAlt
theorem _root_.solution {V W : Ideal (MRing ι)} {f : MRing ι} (hW : W ∉ divSupp V f) :
    divCycle V f W = 0 := by
  classical
  simp [divCycle, Finsupp.ofSupportFinite_coe, hW]
end GroundTheory.Heights₂.Heights.Inter.SwapCyclesAlt
