-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_height_eq_intersectionHeight_4dccfce91942
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:58:52.56924+00:00
-- url     : https://prove2.me/submissions/8c99dccf-decb-4f21-8a1b-b067fe217ac6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_IsSaturatedFirstCoordinateLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_Height
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_CurveIsOrbit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_NoCommonZeroComplex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Reading
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_MemMCoordIdealIffOfIsWeightedHomogeneous
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HeightAsIntersection_proof_9d47be4786fd


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
theorem _root_.solution [Nonempty ι] (h₁ : OrbitCurve.Statement) (h₂ : OrbitDegree.Statement)
    (h₃ : HeightRecR.Statement)
    (II : Ideal (MvPolynomial (Coord n) ℤ) → (m : ℕ) → (Fin m → Geo.HermLine (blockIdx n)) → ℝ)
    (hII : Geo.IsIntersectionFamily II) (A : HermLine n) {x : Cone n (AlgebraicClosure ℚ)}
    (hx : BlockNonzero x) : height A x = IndefiniteRowSideFullHecke.HeightsSet.height II A.toGeo (orbitIdeal x) :=
  HeightAsIntersection.proof h₁ h₂ h₃ ι n II hII A x hx
end GroundTheory.Heights₂.Heights
