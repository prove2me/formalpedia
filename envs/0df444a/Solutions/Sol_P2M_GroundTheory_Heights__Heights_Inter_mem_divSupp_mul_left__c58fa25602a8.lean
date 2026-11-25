-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_mem_divSupp_mul_left__c58fa25602a8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:43:32.916316+00:00
-- url     : https://prove2.me/submissions/8b7d48d4-767f-4267-8bd2-d72662f5fcb7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemDivSuppOfDivCycleNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsMultiHomogTwoXc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_MultAtHorizontalEqZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsHorizontalOfDimOne
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_eq_of_le_of_mem_minimalPrimes


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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2
noncomputable section
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution {P W : Ideal (MRing ι)} (hP : P.IsPrime) {f g : MRing ι}
    (hgP : g ∉ P) (hW : W ∈ divSupp P f) : W ∈ divSupp P (f * g) := by
  refine ⟨⟨⟨hW.1.1.1, (sup_span_mul_le P f g).trans hW.1.1.2⟩, fun Q hQ hQW => ?_⟩, hW.2⟩
  have hfg : f * g ∈ Q := hQ.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  rcases hQ.1.mem_or_mem hfg with hf | hg
  · exact hW.1.2 ⟨hQ.1, sup_le (le_sup_left.trans hQ.2) (Ideal.span_singleton_le_iff_mem _ |>.mpr hf)⟩
      hQW
  · exact (eq_of_le_of_mem_minimalPrimes hP hW.1 hQ.1 (le_sup_left.trans hQ.2) hg hgP hQW).ge
end GroundTheory.Heights₂.Heights.Inter
