-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_unitPoint_birational_ae4e85ff5628
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:11:33.178686+00:00
-- url     : https://prove2.me/submissions/589832fc-aaca-488e-aa97-ff27c356f2fc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Examples
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightObjects
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_TargetSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Reading

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
theorem _root_.solution : Geo.Birational (ι := blockIdx fun _ : Unit ↦ 0) unitPoint := by
  have hC : ∀ a : ℤ, Geo.IsMultiHomog (ι := blockIdx fun _ : Unit ↦ 0)
      (C a : MvPolynomial (Coord fun _ : Unit ↦ 0) ℤ) 0 := by
    intro a m hm k
    have hm0 : m = 0 := by
      by_contra h0
      exact (mem_support_iff.mp hm) (by rw [coeff_C, if_neg (Ne.symm h0)])
    simp [hm0]
  intro s
  refine ⟨0, C s.num, C (s.den : ℤ), hC _, hC _, ?_, ?_⟩
  · simp
  · have hv : ∀ a : ℤ, aeval unitPoint (C a : MvPolynomial (Coord fun _ : Unit ↦ 0) ℤ) = (a : ℚ) :=
      fun a ↦ by rw [aeval_C]; simp
    rw [hv, hv]
    push_cast
    exact (Rat.mul_den_eq_num s).symm
end GroundTheory.Heights₂.Heights
