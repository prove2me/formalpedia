-- Prove2me | solution 1 for PI.QnWCellW.swp_swp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:10:37.705971+00:00
-- url     : https://prove2.me/submissions/671c11dc-ad96-435b-b091-cc38cf8d406c

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
namespace PI.QnWCellW
theorem _root_.solution (k r : ℕ) (p : Fin (2 * r + k + 1)) : swp k r (swp k r p) = p := by
  have hp := p.isLt
  apply Fin.ext
  rw [swp_val, swp_val]
  split_ifs <;> omega
end PI.QnWCellW
