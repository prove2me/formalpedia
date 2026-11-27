-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_exists_point_of_curve_6896801e5e6b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:10:47.088117+00:00
-- url     : https://prove2.me/submissions/0251b8d2-f7e6-441c-b4ce-c8ff57e76149

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_IsSaturatedFirstCoordinateLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_Height
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_CurveIsOrbit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_NoCommonZeroComplex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Reading
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_MemMCoordIdealIffOfIsWeightedHomogeneous
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_mem_points_iff_le_orbitIdeal_894653e45a73

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
theorem _root_.solution (hC : CurveIsOrbit.Statement) (P : ArithVariety n)
    {W : Ideal (MvPolynomial (Coord n) ℤ)} (hW : Geo.IsArithVar (ι := blockIdx n) W 1)
    (hPW : P.ideal ≤ W) : ∃ x ∈ P.points (AlgebraicClosure ℚ), W = orbitIdeal x := by
  obtain ⟨x, hx, rfl⟩ := hC ι n W hW
  exact ⟨x, (mem_points_iff_le_orbitIdeal P x).mpr ⟨hx, hPW⟩, rfl⟩
end GroundTheory.Heights₂.Heights
