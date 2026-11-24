-- Prove2me | solution 1 for PI.QnWCellW.cN_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:51:25.718672+00:00
-- url     : https://prove2.me/submissions/2a3a3af3-4bed-4256-aea1-739800df3ea8

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylCellRange_ReflectionMultiplicationOnBigCell

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open PI PI.QnWCellW
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
namespace PI.QnWCellW
theorem _root_.solution (r : ℕ) (c : Fin r → ℂ) (a : Fin r) : cN r c a.val = c a := by
  simp [cN, a.isLt]
end PI.QnWCellW
