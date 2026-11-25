-- Prove2me | solution 1 for PositivityTheory.ThKEnd.Two.diff_uni
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:59:24.142798+00:00
-- url     : https://prove2.me/submissions/beeba2fb-8698-457e-8466-b2cba0659ef2

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
theorem _root_.solution (κ y : SL(2, R)) (w : R) :
    (κ⁻¹ * y).1 - (κ⁻¹ * ((uni (.ofAdd w))⁻¹ * y)).1 = w • ((κ⁻¹).1 * !![0, 1; 0, 0] * y.1) := by
  rw [← map_inv, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    ← Matrix.mul_sub, Matrix.mul_assoc, ← Matrix.mul_smul, ← Matrix.smul_mul]
  congr 1
  conv_lhs => enter [1]; rw [← Matrix.one_mul y.1]
  rw [← Matrix.sub_mul, uni_val]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp
end PositivityTheory.ThKEnd.Two
