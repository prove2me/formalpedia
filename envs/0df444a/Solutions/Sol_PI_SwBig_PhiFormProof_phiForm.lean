-- Prove2me | solution 1 for PI.SwBig.PhiFormProof.phiForm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:34:57.083971+00:00
-- url     : https://prove2.me/submissions/7f21fdb9-22d3-4f19-b185-a94a295848d2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LongWeylElementSquare
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PhiBigCellForm_BigCellEqW0BMulTM
import Theorems.Thm_PI_SwBig_PhiFormProof_bigCell_eq_w0B_mul_tM
import Theorems.Thm_PI_SwBig_PhiFormProof_exp_neg_eq_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.SwBig PI.SwBig.PhiFormProof
open PI.SwBig
attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra
namespace PI.SwBig.PhiFormProof
theorem _root_.solution : PhiForm := by
  intro k r X x Z X'
  rw [Phi, exp_neg_eq_inv, bigCell_eq_w0B_mul_tM]
  simp only [Matrix.mul_assoc]
end PI.SwBig.PhiFormProof
