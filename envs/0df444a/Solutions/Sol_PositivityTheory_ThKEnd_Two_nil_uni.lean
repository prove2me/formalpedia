-- Prove2me | solution 1 for PositivityTheory.ThKEnd.Two.nil_uni
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:59:56.590491+00:00
-- url     : https://prove2.me/submissions/085d04f9-8cde-4a08-a24a-4c070dee9548

import Definitions.Def_Development_WeilBound_ThetaLifts_EigenvalueEndgame_SignatureSplitting_ConvCont
import Definitions.Def_Development_WeilBound_ThetaLifts_EigenvalueEndgame_SignatureSplitting_ClosedEmb
import Theorems.Thm_PositivityTheory_ThKEnd_Two_uni_val

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option linter.unusedSectionVars false
open PositivityTheory PositivityTheory.ThKEnd PositivityTheory.ThKEnd.Two
open MeasureTheory Topology Filter Matrix NumberField IsDedekindDomain
open scoped Pointwise MatrixGroups
variable {R : Type} [CommRing R]
variable [TopologicalSpace R] [IsTopologicalRing R]
namespace PositivityTheory.ThKEnd.Two
theorem _root_.solution (y : SL(2, R)) (w : R) : !![0, 1; 0, 0] * ((uni (.ofAdd w))⁻¹ * y).1 = !![0, 1; 0, 0] * y.1 := by
  rw [← map_inv, Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mul_assoc, uni_val]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]
end PositivityTheory.ThKEnd.Two
