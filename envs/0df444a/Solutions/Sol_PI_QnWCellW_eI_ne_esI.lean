-- Prove2me | solution 1 for PI.QnWCellW.eI_ne_esI
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:48:28.990506+00:00
-- url     : https://prove2.me/submissions/07439750-51f7-47ef-ab6a-d75b2d52f7b4

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
theorem _root_.solution (k r : ℕ) (l : Fin r) : eI k r l ≠ esI k r l := by
  intro h
  have hl := l.isLt
  rw [Fin.ext_iff] at h
  change l.val = 2 * r + k - l.val at h
  omega
end PI.QnWCellW
