-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_cycR_eq_sum_15b112079e4e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:57:12.177253+00:00
-- url     : https://prove2.me/submissions/fbae7517-fde9-4774-bcf9-446e96546927

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemDivSuppOfDivCycleNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsMultiHomogTwoXc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_MultAtHorizontalEqZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsHorizontalOfDimOne

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
theorem _root_.solution (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (P : Ideal (MRing ι))
    {n : ℕ} (L : Fin n → HermLine ι) (s : MRing ι) :
    cycR I P L s = (divCycle P s).sum fun W m => (m : ℝ) * cycWeight I L W := by
  classical
  unfold cycR
  rw [finsum_mem_def, finsum_eq_sum_of_support_subset _ (s := (divCycle P s).support)]
  · refine Finset.sum_congr rfl fun W _ => ?_
    by_cases h : W ∈ divSupp P s
    · simp [Set.indicator, h, divCycle, Finsupp.ofSupportFinite_coe, cycWeight]
    · simp [Set.indicator, h, divCycle, Finsupp.ofSupportFinite_coe]
  · intro W hW
    rw [Function.mem_support] at hW
    rw [Finset.mem_coe, Finsupp.mem_support_iff]
    intro h0
    apply hW
    by_cases h : W ∈ divSupp P s
    · have : multAt (P ⊔ Ideal.span {s}) W = 0 := by
        simpa [divCycle, Finsupp.ofSupportFinite_coe, h] using h0
      simp [Set.indicator, h, this]
    · simp [Set.indicator, h]
end GroundTheory.Heights₂.Heights.Inter
