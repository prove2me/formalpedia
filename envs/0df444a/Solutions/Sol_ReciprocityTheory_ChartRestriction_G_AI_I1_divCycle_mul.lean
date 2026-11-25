-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.I1.divCycle_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:51:25.675743+00:00
-- url     : https://prove2.me/submissions/1fc192c1-8953-450a-b8d0-f755d2f819b2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_IsFieldIntersection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthCokerEqKerAddDimOneOrderSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CycDim
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemDivSuppOfDivCycleNeZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_locLen_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_locLen_ne_top
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_multAt_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_mem_divSupp_mul_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_mem_divSupp_of_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_mem_of_mem_divSupp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_locLen_quot_eq_zero

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
namespace ReciprocityTheory.ChartRestriction.G.AI.I1
theorem _root_.solution {V : Ideal (MRingOver F ι)} (hV : V.IsPrime) {f g : MRingOver F ι}
    (hf : f ∉ V) (hg : g ∉ V) : divCycle V (f * g) = divCycle V f + divCycle V g := by
  classical
  ext W
  simp only [Finsupp.add_apply, divCycle, Finsupp.ofSupportFinite_coe]
  by_cases h : W ∈ divSupp V (f * g)
  · have hWp := h.1.1.1
    have h' : W ∈ divSupp V (g * f) := by rwa [mul_comm]
    have key := locLen_mul hV hf g ⟨W, hWp⟩
    have hfin := locLen_ne_top h.1
    rw [key] at hfin
    rw [if_pos h, multAt_eq _ _ hWp, key]
    by_cases hfW : f ∈ W <;> by_cases hgW : g ∈ W
    · rw [if_pos (mem_divSupp_of_mul h hfW), if_pos (mem_divSupp_of_mul h' hgW),
        multAt_eq _ _ hWp, multAt_eq _ _ hWp, ENat.toNat_add (WithTop.add_ne_top.mp hfin).1
          (WithTop.add_ne_top.mp hfin).2, add_comm]
    · rw [if_pos (mem_divSupp_of_mul h hfW), if_neg fun h2 => hgW (mem_of_mem_divSupp h2),
        multAt_eq _ _ hWp, locLen_quot_eq_zero _ hgW, zero_add, add_zero]
    · rw [if_neg fun h2 => hfW (mem_of_mem_divSupp h2), if_pos (mem_divSupp_of_mul h' hgW),
        multAt_eq _ _ hWp, locLen_quot_eq_zero (V := V) (g := f) _ hfW, add_zero, zero_add]
    · exact absurd (hWp.mem_or_mem (mem_of_mem_divSupp h)) (by tauto)
  · rw [if_neg h, if_neg fun h2 => h (mem_divSupp_mul_left hV hg h2),
      if_neg fun h2 => h (by rw [mul_comm]; exact mem_divSupp_mul_left hV hf h2)]
end ReciprocityTheory.ChartRestriction.G.AI.I1
