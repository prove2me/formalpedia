-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_RegularityRelativeClosedPoint_killBlocks_comp_eb0db3f96410
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:53:17.032928+00:00
-- url     : https://prove2.me/submissions/ca54dac2-18dd-42fb-ab5b-88598a6a9d5c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsMoreExtra
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsUnitOfNumMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PHorizNotMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_CardLeRingKrullDim

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.RegularityRelativeClosedPoint
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] [DecidableEq K]
omit [Fintype K] [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter.RegularityRelativeClosedPoint
theorem _root_.solution {S T : Finset K} (hST : S ⊆ T) :
    (killBlocks T).comp (killBlocks S) = (killBlocks T : MRing ι →ₐ[ℤ] MRing ι) := by
  refine MvPolynomial.algHom_ext fun p => ?_
  simp only [AlgHom.comp_apply, killBlocks, aeval_X]
  by_cases h : p.1 ∈ S
  · simp [h, hST h]
  · simp [h]
end GroundTheory.Heights₂.Heights.Inter.RegularityRelativeClosedPoint
