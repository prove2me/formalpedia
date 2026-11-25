-- Prove2me | solution 1 for PI.DatumConjInvWork.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:39:06.579943+00:00
-- url     : https://prove2.me/submissions/6e221228-5589-47e1-9b6f-05d7eb5b0a21

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DatumConjInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ConjugationInvariance_SecondRowsBlockDiagMul
import Theorems.Thm_PI_DatumConjInvWork_firstRows_mul
import Theorems.Thm_PI_DatumConjInvWork_secondRows_mul
import Theorems.Thm_PI_DatumConjInvWork_firstRows_blockDiag_mul
import Theorems.Thm_PI_DatumConjInvWork_secondRows_blockDiag_mul
import Theorems.Thm_PI_DatumConjInvWork_II_iff
import Theorems.Thm_PI_DatumConjInvWork_top_iff

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
theorem _root_.solution : PI.DatumConjInv := by
  unfold PI.DatumConjInv
  intro F _ O ϖ a t k hk x
  simp only [Formalism.DoubleCosetMeasures.phiU, MonoidHom.one_apply, Units.val_one]
  split_ifs with h1 h2 h2 <;> first
    | rfl
    | (exfalso
       rw [firstRows_mul, firstRows_blockDiag_mul, secondRows_mul, secondRows_blockDiag_mul, top_iff O ϖ k hk, II_iff O ϖ k hk] at h1
       exact h2 h1)
    | (exfalso
       rw [firstRows_mul, firstRows_blockDiag_mul, secondRows_mul, secondRows_blockDiag_mul, top_iff O ϖ k hk, II_iff O ϖ k hk] at h1
       exact h1 h2)
end PI.DatumConjInvWork
