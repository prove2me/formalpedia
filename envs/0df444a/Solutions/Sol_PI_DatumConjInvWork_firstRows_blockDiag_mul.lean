-- Prove2me | solution 1 for PI.DatumConjInvWork.firstRows_blockDiag_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:34:49.342465+00:00
-- url     : https://prove2.me/submissions/901c1cf6-663b-44fd-8902-8d99daedeaf2

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
    toRows₁ (fromBlocks A 0 0 (1 : Matrix (Fin t) (Fin t) F) * x) = A * toRows₁ x := by
  ext i j
  simp [Matrix.toRows₁, Matrix.mul_apply, Fintype.sum_sum_type]
end PI.DatumConjInvWork
