-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_monomialsBounded_zero_9448bd605ed5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:11:51.394813+00:00
-- url     : https://prove2.me/submissions/16cf335c-77fa-4bb3-91b6-61c906f4c9c6

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
theorem _root_.solution (Q : Ideal (MvPolynomial (Coord n) ℤ)) :
    Geo.MonomialsBounded (ι := blockIdx n) Q ((HermLine.standard n).pow 0).toGeo 0 := by
  intro z hz μ hμ
  have h0 : ∀ p, μ p = 0 := fun p ↦ by
    have := hμ p.1
    rw [Pi.zero_apply, Finset.sum_eq_zero_iff] at this
    exact this p.2 (Finset.mem_univ _)
  have hz' : BlockNonzero (unflatCone z) := (blockNonzero_unflatCone_iff z).mpr hz.1
  rw [HermLine.toGeo_h_of_blockNonzero _ hz']
  simp [h0, HermLine.pow]
end GroundTheory.Heights₂.Heights
