-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_orbitIdeal_curve_of_mem_points_f73930c82716
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:10:28.26335+00:00
-- url     : https://prove2.me/submissions/0ff47686-08b0-405d-877c-b0f105cbb0ae

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
theorem _root_.solution [Nonempty ι] (h₁ : OrbitCurve.Statement)
    (P : ArithVariety n) {x : Cone n (AlgebraicClosure ℚ)}
    (hx : x ∈ P.points (AlgebraicClosure ℚ)) :
    Geo.IsArithVar (ι := blockIdx n) (orbitIdeal x) 1 ∧ P.ideal ≤ orbitIdeal x :=
  ⟨h₁ ι n x hx.1, ((mem_points_iff_le_orbitIdeal P x).mp hx).2⟩
end GroundTheory.Heights₂.Heights
