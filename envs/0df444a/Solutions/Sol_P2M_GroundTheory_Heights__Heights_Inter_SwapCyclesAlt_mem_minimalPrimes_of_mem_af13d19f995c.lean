-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_SwapCyclesAlt_mem_minimalPrimes_of_mem_af13d19f995c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:33:45.219226+00:00
-- url     : https://prove2.me/submissions/33e6160d-d16a-498f-b83b-fceeb656518e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSwapCyclesArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSwap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_NotRelevantOfDimZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemMinimalPrimesOfMemDivSuppDivSupp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSwapCycles
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SwapCyclesAlt_not_lt_lt_9447da08df4b

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
namespace GroundTheory.Heights₂.Heights.Inter.SwapCyclesAlt
theorem _root_.solution {R : Type*} [CommRing R] [IsNoetherianRing R] {P W : Ideal R}
    [P.IsPrime] {a b : R} (hW : W ∈ (P ⊔ Ideal.span {a}).minimalPrimes) (hbP : b ∉ P)
    (hbW : b ∈ W) : W ∈ (P ⊔ Ideal.span {b}).minimalPrimes := by
  have hPW : P ≤ W := le_sup_left.trans hW.1.2
  refine ⟨⟨hW.1.1, sup_le hPW (Ideal.span_le.mpr (by simpa using hbW))⟩,
    fun Q ⟨hQ, hQle⟩ hQW => ?_⟩
  by_contra hWQ
  have hlt : Q < W := lt_of_le_of_ne hQW fun e => hWQ (le_of_eq e.symm)
  have hbQ : b ∈ Q := hQle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self b))
  have hPQ : P < Q := lt_of_le_of_ne (le_sup_left.trans hQle) fun e => hbP (by rw [e]; exact hbQ)
  haveI := hQ
  exact not_lt_lt hW hPQ hlt
end GroundTheory.Heights₂.Heights.Inter.SwapCyclesAlt
