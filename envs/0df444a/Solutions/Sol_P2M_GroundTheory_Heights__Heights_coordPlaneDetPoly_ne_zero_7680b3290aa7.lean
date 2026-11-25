-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_coordPlaneDetPoly_ne_zero_7680b3290aa7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:26:30.09873+00:00
-- url     : https://prove2.me/submissions/a1615db4-a847-46d5-a7f4-77236ae37301

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeFibreAverage
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeIntegralMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PPointLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeMassOfFibre
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_eval_coordPlaneDetPoly_d84d2f98ec4d

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
open MvPolynomial MeasureTheory Module
open scoped ENNReal
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (m k : ℕ) : coordPlaneDetPoly m k ≠ 0 := by
  intro h0
  have h1 := eval_coordPlaneDetPoly (m := m) (k := k)
    (fun ij => if ij.2 = Fin.castAdd k ij.1 then 1 else 0)
  have hone : coordPlaneBlock (Function.curry fun ij : Fin m × Fin (m + k) =>
      if ij.2 = Fin.castAdd k ij.1 then (1 : ℂ) else 0) = 1 := by
    ext i j
    simp [coordPlaneBlock, Function.curry, Matrix.one_apply, eq_comm]
  rw [h0, map_zero, hone, Matrix.det_one] at h1
  exact zero_ne_one h1
end GroundTheory.Heights₂.Heights
