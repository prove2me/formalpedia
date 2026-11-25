-- Prove2me | solution 1 for PI.QnWCellW.cN_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:12:18.554426+00:00
-- url     : https://prove2.me/submissions/13373c75-cfa3-497b-b41a-6bfa4a42d08a

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
theorem _root_.solution (r : ℕ) (c : Fin r → ℂ) (j : ℕ) (h : j < r) : c ⟨j, h⟩ = cN r c j := by
  unfold cN
  rw [dif_pos h]
end PI.QnWCellW
