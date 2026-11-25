-- Prove2me | solution 1 for PI.QnWCellW.cN_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:12:22.586735+00:00
-- url     : https://prove2.me/submissions/801ff1ab-a77e-425f-a3c8-1df30eb04019

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
theorem _root_.solution (r j : ℕ) : cN r (fun _ => 1) j = if j < r then 1 else 0 := by
  unfold cN
  split_ifs <;> rfl
end PI.QnWCellW
