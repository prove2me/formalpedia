-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_normSqE_pos_5cb9d9b38f7b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:48:31.715033+00:00
-- url     : https://prove2.me/submissions/ea451a30-494e-4a53-81fe-d995325c9c56

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ArithmeticHilbertSamuelLowerBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsSmoothPts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ArithModel
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_zero_4f3b615e7508
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_one_661faae583ac
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_eL_apply_0119d81ffd10
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine.y_zero
attribute [local simp] GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine.y_one

set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine
open scoped Topology
variable {J : Type} [Fintype J]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine
theorem _root_.solution {z : J → ℂ} (hz : z ≠ 0) : 0 < normSqE z := by
  unfold normSqE
  have : eL z ≠ 0 := fun h => hz (by
    have := congrArg (fun v : EuclideanSpace ℂ J => v.ofLp) h
    simpa [eL_apply] using this)
  positivity
end GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine
