-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ArithVariety_mem_mcPts_iff_497efdbb0f6c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:54:22.83736+00:00
-- url     : https://prove2.me/submissions/d4e7105a-9e08-4fcd-82b5-ece1abb40799

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ArithmeticHilbertSamuelLowerBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_RationalSections_IsRatSectionOn
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightObjects
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_eval_map_flatCone_f6bc8e6a8518

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
variable {ι : Type} {n : ι → ℕ}
variable [Fintype ι] [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights
namespace ArithVariety
theorem _root_.solution (P : ArithVariety n) (w : Coord n → ℂ) :
    w ∈ Geo.mcPts P.ideal ↔ unflatCone w ∈ P.points ℂ := by
  rw [ArithVariety.points, Set.mem_setOf_eq, blockNonzero_unflatCone_iff, Geo.mcPts,
    Set.mem_setOf_eq]
  refine and_congr Iff.rfl (forall₂_congr fun f _ ↦ ?_)
  rw [← eval_map_flatCone, flatCone_unflatCone]
end ArithVariety
end GroundTheory.Heights₂.Heights
