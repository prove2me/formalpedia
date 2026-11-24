-- Prove2me | solution 1 for PI.QnWCellW.swp_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:57:19.073806+00:00
-- url     : https://prove2.me/submissions/a00eb5d3-c04d-404e-9cf8-337cf167aaf4

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
theorem _root_.solution (k r : ℕ) (p : Fin (2 * r + k + 1)) :
    (swp k r p).val = if r ≤ p.val ∧ p.val ≤ r + k then p.val else 2 * r + k - p.val := by
  unfold swp
  split_ifs <;> rfl
end PI.QnWCellW
