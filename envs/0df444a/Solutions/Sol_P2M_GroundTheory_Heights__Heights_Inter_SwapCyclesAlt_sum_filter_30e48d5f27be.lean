-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_SwapCyclesAlt_sum_filter_30e48d5f27be
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:57:53.977138+00:00
-- url     : https://prove2.me/submissions/06262cf5-3e22-4462-a0a6-2ed474a853f5

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
theorem _root_.solution (p : Ideal (MRing ι) → Prop) [DecidablePred p] (c : Ideal (MRing ι) →₀ ℕ)
    (D : Ideal (MRing ι) → Ideal (MRing ι) →₀ ℕ) :
    (c.sum fun W m => m • (D W).filter p) = (c.sum fun W m => m • D W).filter p := by
  ext U
  rw [Finsupp.filter_apply, Finsupp.sum_apply, Finsupp.sum_apply]
  split_ifs with hU
  · simp only [Finsupp.smul_apply, Finsupp.filter_apply, if_pos hU]
  · simp [Finsupp.smul_apply, Finsupp.filter_apply, if_neg hU, Finsupp.sum]
end GroundTheory.Heights₂.Heights.Inter.SwapCyclesAlt
