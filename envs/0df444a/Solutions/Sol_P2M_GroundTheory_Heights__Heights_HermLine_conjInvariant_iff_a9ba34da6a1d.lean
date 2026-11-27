-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HermLine_conjInvariant_iff_a9ba34da6a1d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:54:59.864078+00:00
-- url     : https://prove2.me/submissions/dd93d19f-95b8-4a69-916f-ce998db153d2

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
namespace GroundTheory.Heights₂.Heights
namespace HermLine
theorem _root_.solution (A : HermLine n) :
    A.ConjInvariant ↔ Geo.IsConjInvariantH A.toGeo := by
  have hb : ∀ w : Coord n → ℂ, BlockNonzero (unflatCone fun p ↦ starRingEnd ℂ (w p)) ↔
      BlockNonzero (unflatCone w) := by
    intro w
    simp only [blockNonzero_unflatCone_iff, ne_eq, map_eq_zero]
  constructor
  · intro h w
    by_cases hw : BlockNonzero (unflatCone w)
    · rw [A.toGeo_h_of_blockNonzero hw, A.toGeo_h_of_blockNonzero ((hb w).mpr hw)]
      exact h _ hw
    · simp only [toGeo, if_neg hw, if_neg (fun h' ↦ hw ((hb w).mp h'))]
  · intro h z hz
    have hz' : BlockNonzero (unflatCone (flatCone z)) := hz
    have := h (flatCone z)
    rw [A.toGeo_h_of_blockNonzero hz', A.toGeo_h_of_blockNonzero ((hb _).mpr hz')] at this
    exact this
end HermLine
end GroundTheory.Heights₂.Heights
