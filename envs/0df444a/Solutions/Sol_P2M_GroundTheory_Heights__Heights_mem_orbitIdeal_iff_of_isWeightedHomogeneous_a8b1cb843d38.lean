-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_mem_orbitIdeal_iff_of_isWeightedHomogeneous_a8b1cb843d38
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:53:13.968977+00:00
-- url     : https://prove2.me/submissions/b90cb986-5f8f-47cf-9680-053de959905c

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
theorem _root_.solution (x : Cone n (AlgebraicClosure ℚ))
    {g : MvPolynomial (Coord n) ℤ} {m : ι → ℕ} (hg : IsWeightedHomogeneous (coordDeg n) g m) :
    g ∈ orbitIdeal x ↔ evalCone x g = 0 := by
  rw [orbitIdeal, mem_mCoordIdeal_iff_of_isWeightedHomogeneous _ hg, aeval_flatCone]
end GroundTheory.Heights₂.Heights
