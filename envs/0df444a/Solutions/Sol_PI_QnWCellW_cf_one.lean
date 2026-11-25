-- Prove2me | solution 1 for PI.QnWCellW.cf_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:16:59.387087+00:00
-- url     : https://prove2.me/submissions/0e6f17b3-3ff7-4195-aebe-5c35b7e8a750

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylCellRange_ReflectionMultiplicationOnBigCell
import Theorems.Thm_PI_QnWCellW_cN_val
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
theorem _root_.solution (k r : ℕ) (p : Fin (2 * r + k + 1)) : cf k r (fun _ => 1) p = 1 := by
  have hp := p.isLt
  simp only [cf, cN]
  split_ifs <;> first | omega | simp
end PI.QnWCellW
