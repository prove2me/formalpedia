-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.I1.DivisorCycleSwap.cast_multAt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:29:40.1076+00:00
-- url     : https://prove2.me/submissions/9bbc066a-ee38-4541-9897-6df9aba8dbcc

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemDivSuppOfDivCycleNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_SwapLoc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemMinimalPrimesOfMemDivSuppDivSupp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_SwapLoc_lenAt_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_locLen_ne_top
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_multAt_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {F : Type*} [Field F]
open SwapLoc
open ReciprocityTheory.ChartRestriction.G.AI.I1.DivisorCycleSwap
namespace ReciprocityTheory.ChartRestriction.G.AI.I1.DivisorCycleSwap
theorem _root_.solution {J W : Ideal (MRingOver F ι)} [hW : W.IsPrime] (hJ : W ∈ J.minimalPrimes) :
    ((multAt J W : ℕ) : ℕ∞) = lenAt J W := by
  rw [multAt_eq J W hW, ENat.coe_toNat (locLen_ne_top hJ), lenAt_eq]
  rfl
end ReciprocityTheory.ChartRestriction.G.AI.I1.DivisorCycleSwap
