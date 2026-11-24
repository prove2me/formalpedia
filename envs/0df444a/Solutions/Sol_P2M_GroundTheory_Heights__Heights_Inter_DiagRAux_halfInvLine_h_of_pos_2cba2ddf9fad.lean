-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_halfInvLine_h_of_pos_2cba2ddf9fad
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:56:21.006071+00:00
-- url     : https://prove2.me/submissions/9107a36f-0103-40e2-8bbd-e269b7bbc9fa

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagR
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.Inter.DiagRAux
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter.DiagRAux
theorem _root_.solution (A B : HermLine ι) (c : K → ℤ) (hc : ∀ k, 2 * c k = -(A.a k + B.a k))
    (z : (Σ k, ι k) → ℂ) (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    (halfInvLine A B c hc).h z = (A.h z * B.h z) ^ (-(1 / 2 : ℝ)) := by
  simp only [halfInvLine, abs_of_pos (mul_pos (A.pos z hz) (B.pos z hz))]
end GroundTheory.Heights₂.Heights.Inter.DiagRAux
