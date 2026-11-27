-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_height_congr_metric_78f42bd42780
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:18:48.3038+00:00
-- url     : https://prove2.me/submissions/ccfb8800-cc56-4485-b63e-cc298f33ddc0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_IsSaturatedFirstCoordinateLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_Height
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_CurveIsOrbit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_NoCommonZeroComplex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Reading
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_MemMCoordIdealIffOfIsWeightedHomogeneous
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_blockNonzero_sigma_8db15361a0fa


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
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
open scoped ContDiff
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {A A' : HermLine n} (hdeg : A.deg = A'.deg)
    (hm : ∀ z : Cone n ℂ, BlockNonzero z → A.metric z = A'.metric z)
    {x : Cone n (AlgebraicClosure ℚ)} (hx : BlockNonzero x) : height A x = height A' x := by
  unfold height
  rw [hdeg]
  congr 2
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  rw [hm _ (blockNonzero_sigma hx σ)]
end GroundTheory.Heights₂.Heights
