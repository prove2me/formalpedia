-- Prove2me | solution 1 for PositivityTheory.ThKEnd.Two.uni_dia
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:06:24.353247+00:00
-- url     : https://prove2.me/submissions/6c57a395-4f4f-4e09-972e-6ee0b7128498

import Definitions.Def_Development_WeilBound_ThetaLifts_EigenvalueEndgame_SignatureSplitting_ConvCont
import Definitions.Def_Development_WeilBound_ThetaLifts_EigenvalueEndgame_SignatureSplitting_ClosedEmb
import Theorems.Thm_PositivityTheory_ThKEnd_Two_uni_val
import Theorems.Thm_PositivityTheory_ThKEnd_Two_dia_val

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
namespace PositivityTheory.ThKEnd.Two
theorem _root_.solution (x : R) (u : Rˣ) : uni (.ofAdd x) * dia u = dia u * uni (.ofAdd ((u⁻¹).1 * (u⁻¹).1 * x)) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, uni_val, dia_val, Matrix.mul_fin_two, toAdd_ofAdd]
  congr 3
  all_goals simp only [mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add]
  rw [← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul, mul_comm]
end PositivityTheory.ThKEnd.Two
