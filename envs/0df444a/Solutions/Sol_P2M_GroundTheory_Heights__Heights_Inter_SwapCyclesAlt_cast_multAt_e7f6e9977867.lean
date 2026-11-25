-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_SwapCyclesAlt_cast_multAt_e7f6e9977867
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:57:46.93416+00:00
-- url     : https://prove2.me/submissions/8ded6f9c-277c-49d6-adab-fd63252f3ce1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSwapCyclesArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSwap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_NotRelevantOfDimZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemMinimalPrimesOfMemDivSuppDivSupp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSwapCycles
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_SwapLoc_lenAt_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_locLen_ne_top


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
theorem _root_.solution {J W : Ideal (MRing ι)} [hW : W.IsPrime] (hJ : W ∈ J.minimalPrimes) :
    ((multAt J W : ℕ) : ℕ∞) = lenAt J W := by
  have e : multAt J W = (locLen (MRing ι ⧸ J) ⟨W, hW⟩).toNat := by simp [multAt, hW, locLen]
  rw [e, ENat.coe_toNat (locLen_ne_top hJ), lenAt_eq]
  rfl
end GroundTheory.Heights₂.Heights.Inter.SwapCyclesAlt
