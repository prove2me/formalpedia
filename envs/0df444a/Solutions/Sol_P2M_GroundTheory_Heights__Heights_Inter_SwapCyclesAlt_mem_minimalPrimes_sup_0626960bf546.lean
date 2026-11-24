-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_SwapCyclesAlt_mem_minimalPrimes_sup_0626960bf546
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:57:08.01964+00:00
-- url     : https://prove2.me/submissions/a93ffac9-9392-4cc5-b345-73c8fa500dc4

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
namespace GroundTheory.Heights₂.Heights.Inter.SwapCyclesAlt
theorem _root_.solution {R : Type*} [CommRing R] {V W Z : Ideal R} {f t : R}
    (hZ : Z ∈ (V ⊔ Ideal.span {f} ⊔ Ideal.span {t}).minimalPrimes)
    (hW : W ∈ (V ⊔ Ideal.span {f}).minimalPrimes) (hWZ : W ≤ Z) :
    Z ∈ (W ⊔ Ideal.span {t}).minimalPrimes :=
  ⟨⟨hZ.1.1, sup_le hWZ (le_sup_right.trans hZ.1.2)⟩, fun _ ⟨hQ, hQle⟩ hQZ =>
    hZ.2 ⟨hQ, sup_le (hW.1.2.trans (le_sup_left.trans hQle)) (le_sup_right.trans hQle)⟩ hQZ⟩
end GroundTheory.Heights₂.Heights.Inter.SwapCyclesAlt
