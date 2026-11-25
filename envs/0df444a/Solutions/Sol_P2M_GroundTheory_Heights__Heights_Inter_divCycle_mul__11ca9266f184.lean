-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_divCycle_mul__11ca9266f184
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:50:49.085209+00:00
-- url     : https://prove2.me/submissions/fcb9d5ae-b485-4d3e-b907-ab30347cec68

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemDivSuppOfDivCycleNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsMultiHomogTwoXc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_MultAtHorizontalEqZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsHorizontalOfDimOne
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_mem_of_mem_divSupp__48cdc1ee338b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_mem_divSupp_mul_left__c58fa25602a8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_mem_divSupp_of_mul__e02253524522
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_multAt_eq__979b702317fd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_locLen_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_locLen_ne_top
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_locLen_quot_eq_zero


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
theorem _root_.solution {P : Ideal (MRing ι)} (hP : P.IsPrime) {f g : MRing ι}
    (hf : f ∉ P) (hg : g ∉ P) : divCycle P (f * g) = divCycle P f + divCycle P g := by
  classical
  ext W
  simp only [Finsupp.add_apply, divCycle, Finsupp.ofSupportFinite_coe]
  by_cases h : W ∈ divSupp P (f * g)
  · have hWp := h.1.1.1
    have h' : W ∈ divSupp P (g * f) := by rwa [mul_comm]
    have key := locLen_mul hP hf g ⟨W, hWp⟩
    have hfin := locLen_ne_top h.1
    rw [key] at hfin
    rw [if_pos h, multAt_eq' _ _ hWp, key]
    by_cases hfW : f ∈ W <;> by_cases hgW : g ∈ W
    · rw [if_pos (mem_divSupp_of_mul' h hfW), if_pos (mem_divSupp_of_mul' h' hgW),
        multAt_eq' _ _ hWp, multAt_eq' _ _ hWp, ENat.toNat_add (WithTop.add_ne_top.mp hfin).1
          (WithTop.add_ne_top.mp hfin).2, add_comm]
    · rw [if_pos (mem_divSupp_of_mul' h hfW), if_neg fun h2 => hgW (mem_of_mem_divSupp' h2),
        multAt_eq' _ _ hWp, locLen_quot_eq_zero _ hgW, zero_add, add_zero]
    · rw [if_neg fun h2 => hfW (mem_of_mem_divSupp' h2), if_pos (mem_divSupp_of_mul' h' hgW),
        multAt_eq' _ _ hWp, locLen_quot_eq_zero (V := P) (g := f) _ hfW, add_zero, zero_add]
    · exact absurd (hWp.mem_or_mem (mem_of_mem_divSupp' h)) (by tauto)
  · rw [if_neg h, if_neg fun h2 => h (mem_divSupp_mul_left' hP hg h2),
      if_neg fun h2 => h (by rw [mul_comm]; exact mem_divSupp_mul_left' hP hf h2)]
end GroundTheory.Heights₂.Heights.Inter
