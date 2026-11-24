-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_monomialValues_zero_a00cab2fcc08
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:04:41.630156+00:00
-- url     : https://prove2.me/submissions/0313e7ae-0a11-45cb-a71b-189c98547ff8

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
omit [Fintype ι] [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution [Fintype ι] {Ω : Type} [Field Ω] (y : Coord n → Ω) :
    monomialValues y 0 = {1} := by
  ext s
  constructor
  · rintro ⟨μ, hμ, rfl⟩
    have h0 : ∀ p, μ p = 0 := fun p ↦ by
      have := hμ p.1
      rw [Pi.zero_apply, Finset.sum_eq_zero_iff] at this
      exact this p.2 (Finset.mem_univ _)
    simp [h0]
  · rintro rfl
    exact ⟨0, fun k ↦ by simp, by simp⟩
end GroundTheory.Heights₂.Heights
