-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_whole_one_normal_c1b5abb0aa54
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:40:36.288971+00:00
-- url     : https://prove2.me/submissions/1f2212db-8ded-4681-8bac-7ad3c213ebca

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Examples
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightObjects
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_TargetSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Reading
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_whole_mkF_injective_f0f5f10d0d70


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ReciprocityTheory.ChartRestriction.G
open scoped ContDiff
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
variable (n)
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (L : HermLine n) :
    (ArithVariety.whole n).IsNormalSection (L.pow 0).deg 1 ∧
      (ArithVariety.whole n).IsSmallFor (L.pow 0) 1 := by
  have hd : (L.pow 0).deg = 0 := by
    funext k
    simp [HermLine.pow]
  refine ⟨⟨⟨1, 1, 0, 0, isWeightedHomogeneous_one ℤ (coordDeg n), isWeightedHomogeneous_one ℤ (coordDeg n),
    fun k ↦ by simp [hd], (Ideal.ne_top_iff_one _).mp (ArithVariety.whole n).isPrime.ne_top, by simp⟩,
    fun c _ ↦ ?_⟩, ?_⟩
  · rw [hd]
    simp only [ArithVariety.chartPow, Pi.zero_apply, zpow_zero, Finset.prod_const_one, div_one]
    exact one_mem _
  · intro p q _ _ _ _ _ h z _
    have hpq : p = q := ArithVariety.whole_mkF_injective n (by rw [h, one_mul])
    rw [hpq]
    change _ ≤ _ * L.metric z ^ 0
    simp
end GroundTheory.Heights₂.Heights
