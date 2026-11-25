-- Prove2me | solution 1 for PI.SwBig.PhiFormProof.bigCell_eq_w0B_mul_tM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:28:37.280788+00:00
-- url     : https://prove2.me/submissions/4aa6fce5-362f-4563-a3d2-3797095afd80

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LongWeylElementSquare
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PhiBigCellForm_BigCellEqW0BMulTM

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
theorem _root_.solution (k r : ℕ) (c : Fin r → ℂ) :
    bigCell k r c 1 = w0B k r * tM k r c := by
  ext i j
  simp only [w0B, tM, Matrix.mul_diagonal, bigCell, tv]
  split_ifs <;> simp_all
end PI.SwBig.PhiFormProof
