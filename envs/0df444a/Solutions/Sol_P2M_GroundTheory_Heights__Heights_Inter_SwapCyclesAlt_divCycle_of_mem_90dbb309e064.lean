-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_SwapCyclesAlt_divCycle_of_mem_90dbb309e064
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:18:16.211812+00:00
-- url     : https://prove2.me/submissions/f8dfcaac-2e90-47ea-9600-18eb88a54e3b

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
theorem _root_.solution {V W : Ideal (MRing ι)} {f : MRing ι} (hW : W ∈ divSupp V f) :
    divCycle V f W = multAt (V ⊔ Ideal.span {f}) W := by
  classical
  simp [divCycle, Finsupp.ofSupportFinite_coe, hW]
end GroundTheory.Heights₂.Heights.Inter.SwapCyclesAlt
