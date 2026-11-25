-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_mem_points_iff_le_orbitIdeal_894653e45a73
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:31:56.242119+00:00
-- url     : https://prove2.me/submissions/333c21dc-77ed-4141-a336-c9f811c30a82

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_IsSaturatedFirstCoordinateLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_Height
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_CurveIsOrbit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_NoCommonZeroComplex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Reading
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_MemMCoordIdealIffOfIsWeightedHomogeneous
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_aeval_flatCone_0f6d6e67785c

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
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (P : ArithVariety n) (x : Cone n (AlgebraicClosure ℚ)) :
    x ∈ P.points (AlgebraicClosure ℚ) ↔ BlockNonzero x ∧ P.ideal ≤ orbitIdeal x := by
  refine and_congr Iff.rfl ⟨fun h f hf ↦ ?_, fun h f hf ↦ ?_⟩
  · rw [orbitIdeal, mem_mCoordIdeal_iff]
    intro m
    rw [aeval_flatCone]
    exact h _ (P.homogeneous f hf m)
  · rw [← aeval_flatCone]
    exact aeval_eq_zero_of_mem_mCoordIdeal _ (h hf)
end GroundTheory.Heights₂.Heights
