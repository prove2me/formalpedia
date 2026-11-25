-- Prove2me | solution 1 for PI.QnWCellW.Wm_empty
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:12:04.106037+00:00
-- url     : https://prove2.me/submissions/bb5f2ccc-7f71-46a7-b42a-a4b52315fc02

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
theorem _root_.solution (k r : ℕ) (c : Fin r → ℂ) : Wm k r ∅ c = 1 := by
  ext p q
  simp [Wm, Matrix.one_apply, Fin.val_inj]
end PI.QnWCellW
