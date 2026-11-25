-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_log_regLine_h_743c8a7df0e2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:25:59.253834+00:00
-- url     : https://prove2.me/submissions/9f55e2ed-13fe-4758-af89-34ff6ef51a4b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheetA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NoCommonComponentCoordinatesPlane
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_RegLine
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regLine_h_c0ca1b0dda44

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
theorem _root_.solution (z : (Σ k, ι k) → ℂ) :
    Real.log ((regLine E t ht ε).h z) = Real.log (secNorm E t z ^ 2 + ε) / 2 := by
  rw [regLine_h, Real.log_exp]
end GroundTheory.Heights₂.Heights.Inter
