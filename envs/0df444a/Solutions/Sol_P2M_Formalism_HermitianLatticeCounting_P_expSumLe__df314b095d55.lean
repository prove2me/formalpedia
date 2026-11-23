-- Prove2me | solution 1 for P2M_Formalism_HermitianLatticeCounting_P_expSumLe__df314b095d55
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:06:46.426918+00:00
-- url     : https://prove2.me/submissions/cb37444d-532a-4da9-9d6e-123b930f0bf0

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : ExpSumLe' := by
  intro A x hA hx
  have h3A : 0 < 3 * A := by linarith
  have hlog : 0 ≤ Real.log (3 * A) := Real.log_nonneg (by linarith)
  have hE : Real.exp (-x / 6) * Real.exp (x / 6) = 1 := by
    rw [← Real.exp_add, show -x / 6 + x / 6 = (0:ℝ) by ring, Real.exp_zero]
  have h3 : 3 * A ≤ Real.exp (x / 6) := by
    calc 3 * A = Real.exp (Real.log (3 * A)) := (Real.exp_log h3A).symm
      _ ≤ Real.exp (x / 6) := Real.exp_le_exp.mpr (by linarith)
  have hpos := Real.exp_pos (-x / 6)
  have hA' : 3 * A * Real.exp (-x / 6) ≤ 1 := by nlinarith
  have hsplit : Real.exp (-x / 2) = Real.exp (-x / 3) * Real.exp (-x / 6) := by
    rw [← Real.exp_add]; congr 1; ring
  have t1 : Real.exp (-4 * x) ≤ Real.exp (-x / 2) := Real.exp_le_exp.mpr (by linarith)
  have t2 : Real.exp (-x) ≤ Real.exp (-x / 2) := Real.exp_le_exp.mpr (by linarith)
  have hp3 := Real.exp_pos (-x / 3)
  have hs : Real.exp (-4 * x) + Real.exp (-x / 2) + Real.exp (-x) ≤ 3 * Real.exp (-x / 2) := by
    linarith
  calc A * (Real.exp (-4 * x) + Real.exp (-x / 2) + Real.exp (-x))
        ≤ A * (3 * Real.exp (-x / 2)) := mul_le_mul_of_nonneg_left hs (by linarith)
    _ = Real.exp (-x / 3) * (3 * A * Real.exp (-x / 6)) := by rw [hsplit]; ring
    _ ≤ Real.exp (-x / 3) * 1 := mul_le_mul_of_nonneg_left hA' hp3.le
    _ = Real.exp (-x / 3) := mul_one _
end Formalism.HermitianLatticeCounting.P
