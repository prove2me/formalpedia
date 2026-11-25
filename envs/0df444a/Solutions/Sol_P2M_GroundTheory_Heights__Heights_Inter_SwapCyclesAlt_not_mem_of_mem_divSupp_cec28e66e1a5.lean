-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_SwapCyclesAlt_not_mem_of_mem_divSupp_cec28e66e1a5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:18:47.750692+00:00
-- url     : https://prove2.me/submissions/1706fb68-3ec6-4c12-8a41-6774dbc85435

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSwapCyclesArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSwap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_NotRelevantOfDimZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemMinimalPrimesOfMemDivSuppDivSupp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSwapCycles
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SwapCyclesAlt_mem_minimalPrimes_of_mem_af13d19f995c

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
theorem _root_.solution {P W : Ideal (MRing ι)} [P.IsPrime] {s s' : MRing ι}
    (hs' : s' ∉ P) (hnc : ∀ W, W ∈ divSupp P s → W ∉ divSupp P s') (hW : W ∈ divSupp P s) :
    s' ∉ W :=
  fun h => hnc W hW ⟨mem_minimalPrimes_of_mem hW.1 hs' h, hW.2⟩
end GroundTheory.Heights₂.Heights.Inter.SwapCyclesAlt
