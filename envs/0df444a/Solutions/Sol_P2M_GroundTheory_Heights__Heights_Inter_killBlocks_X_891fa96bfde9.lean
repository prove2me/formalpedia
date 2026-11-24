-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_killBlocks_X_891fa96bfde9
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:57:14.078346+00:00
-- url     : https://prove2.me/submissions/79104efe-4028-46f3-8d0a-ad385e323b34

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_RationalSections_ThmISt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_UniquenessDegreeFormOfIntersectionForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ArithVarZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
omit [Fintype K] [∀ k, Fintype (ι k)]
open Classical
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution (S : Set K) (p : Σ k, ι k) :
    killBlocks S (X p : MRing ι) = if p.1 ∈ S then 0 else X p := by
  rw [killBlocks, aeval_X]
end GroundTheory.Heights₂.Heights.Inter
