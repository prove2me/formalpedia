-- Prove2me | solution 1 for PI.QnWCellW.Wm_mul_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:12:13.615549+00:00
-- url     : https://prove2.me/submissions/ebe2b536-b059-4230-a503-ec4cc78ded22

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylCellRange_ReflectionMultiplicationOnBigCell
import Theorems.Thm_PI_QnWCellW_cN_val
import Theorems.Thm_PI_QnWCellW_Wm_range_apply
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
theorem _root_.solution (k r : ℕ) (c : Fin r → ℂ) (M : Mx k r) (p q : Fin (2 * r + k + 1)) :
    (Wm k r (Finset.range r) c * M) p q = cf k r c p * M (swp k r p) q := by
  rw [Matrix.mul_apply]
  simp_rw [Wm_range_apply]
  simp [ite_mul]
end PI.QnWCellW
