-- Prove2me | solution 1 for PI.QnWCellW.Wm_range_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:21:19.767124+00:00
-- url     : https://prove2.me/submissions/8d1fb08b-aadb-4885-8502-1e0a966f42c7

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylCellRange_ReflectionMultiplicationOnBigCell
import Theorems.Thm_PI_QnWCellW_cN_val
import Theorems.Thm_PI_QnWCellW_swp_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PI.QnWCellW.cN_val

set_option autoImplicit false
open Matrix Finset
open PI PI.QnWCellW
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
set_option maxHeartbeats 800000
namespace PI.QnWCellW
theorem _root_.solution (k r : ℕ) (c : Fin r → ℂ) (p x : Fin (2 * r + k + 1)) :
    Wm k r (Finset.range r) c p x = if x = swp k r p then cf k r c p else 0 := by
  have hp := p.isLt
  have hx := x.isLt
  simp only [Wm, Finset.mem_range, cf, Fin.ext_iff, swp_val]
  split_ifs <;> first | rfl | (exfalso; omega) | (congr 1 <;> omega) | (congr 1 <;> congr 1 <;> congr 1 <;> omega) | (simp only [star_one, inv_one, mul_one, one_mul, mul_zero, zero_mul, star_zero, _root_.inv_zero] <;> first | rfl | (congr 1 <;> omega) | (congr 1 <;> congr 1 <;> congr 1 <;> omega))
end PI.QnWCellW
