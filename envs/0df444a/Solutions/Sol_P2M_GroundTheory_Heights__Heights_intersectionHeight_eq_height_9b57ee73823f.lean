-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_intersectionHeight_eq_height_9b57ee73823f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:09:32.897259+00:00
-- url     : https://prove2.me/submissions/7b16e8de-5c5d-46ea-8f67-264308987353

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_IsSaturatedFirstCoordinateLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_Height
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_CurveIsOrbit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_NoCommonZeroComplex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Reading
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_MemMCoordIdealIffOfIsWeightedHomogeneous
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_inter_congr_of_curve_deb0aef85e6b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_height_eq_intersectionHeight_4dccfce91942
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermLine_toGeo_ofGeo_h_01fd03adcfe5


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
    (hII : Geo.IsIntersectionFamily II) (B : Geo.HermLine (blockIdx n)) (hB : Geo.IsSmoothHerm B)
    {x : Cone n (AlgebraicClosure ℚ)} (hx : BlockNonzero x) :
    IndefiniteRowSideFullHecke.HeightsSet.height II B (orbitIdeal x) = height (HermLine.ofGeo B hB) x := by
  rw [height_eq_intersectionHeight h₁ h₂ h₃ II hII _ hx]
  unfold IndefiniteRowSideFullHecke.HeightsSet.height
  rw [inter_congr_of_curve II hII (h₁ ι n x hx) hB (HermLine.isSmoothHerm_toGeo _) rfl
    fun z hz ↦ (HermLine.toGeo_ofGeo_h B hB ((blockNonzero_unflatCone_iff z).mpr hz.1)).symm]
end GroundTheory.Heights₂.Heights
