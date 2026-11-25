-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_regLine_a_a2bda8d846c3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:58:30.772831+00:00
-- url     : https://prove2.me/submissions/65d62c5c-53db-4128-925a-12d3b340bc5b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheetA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NoCommonComponentCoordinatesPlane
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_RegLine

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
set_option linter.unusedSectionVars false
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable {E : HermLine ι} {t : MRing ι} {ht : ∃ a : K → ℕ, (∀ k, E.a k = a k) ∧ IsMultiHomog t a}
  {ε : ℝ}
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution : (regLine E t ht ε).a = 0 := rfl
end GroundTheory.Heights₂.Heights.Inter
