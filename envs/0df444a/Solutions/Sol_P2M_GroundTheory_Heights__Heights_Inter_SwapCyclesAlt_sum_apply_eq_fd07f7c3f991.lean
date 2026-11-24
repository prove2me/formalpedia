-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_SwapCyclesAlt_sum_apply_eq_fd07f7c3f991
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:32:19.900249+00:00
-- url     : https://prove2.me/submissions/dda93075-9dd6-4010-8cdc-4139bbeda93b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSwapCyclesArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSwap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_NotRelevantOfDimZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemMinimalPrimesOfMemDivSuppDivSupp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSwapCycles
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SwapCyclesAlt_mem_divSupp_of_ne_zero_0327083d8eb6

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
theorem _root_.solution (V Z : Ideal (MRing ι)) (f t : MRing ι) :
    ((divCycle V f).sum fun W m => m • divCycle W t) Z =
      ∑ W ∈ (divSupp_finite V f).toFinset, divCycle V f W * divCycle W t Z := by
  classical
  have hs : (divCycle V f).support ⊆ (divSupp_finite V f).toFinset := by
    intro W hW
    rw [Finsupp.mem_support_iff] at hW
    exact (divSupp_finite V f).mem_toFinset.mpr (mem_divSupp_of_ne_zero hW)
  rw [Finsupp.sum_apply, Finsupp.sum_of_support_subset _ hs _ (fun _ _ => by simp)]
  simp only [Finsupp.smul_apply, smul_eq_mul]
end GroundTheory.Heights₂.Heights.Inter.SwapCyclesAlt
