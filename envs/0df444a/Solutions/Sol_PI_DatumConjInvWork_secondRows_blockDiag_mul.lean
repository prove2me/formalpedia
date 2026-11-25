-- Prove2me | solution 1 for PI.DatumConjInvWork.secondRows_blockDiag_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:34:58.225948+00:00
-- url     : https://prove2.me/submissions/3668b78e-35c3-419a-b7ac-90343f1cc204

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DatumConjInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ConjugationInvariance_SecondRowsBlockDiagMul

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
open PI PI.DatumConjInvWork
variable {F : Type} [Field F] {a t : ℕ}
namespace PI.DatumConjInvWork
theorem _root_.solution (A : Matrix (Fin a) (Fin a) F) (x : Matrix (Fin a ⊕ Fin t) (Fin a) F) :
    toRows₂ (fromBlocks A 0 0 (1 : Matrix (Fin t) (Fin t) F) * x) = toRows₂ x := by
  ext i j
  simp [Matrix.toRows₂, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
end PI.DatumConjInvWork
