-- Prove2me | solution 1 for PI.OddDualWeyl.Red.rowAct_rowAct
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:12:33.680288+00:00
-- url     : https://prove2.me/submissions/d7a214d2-d5a4-4791-95c0-9660b645be8b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_AevalMulHomog
import Theorems.Thm_PI_OddDualWeyl_Red_sbs_sbs
import Theorems.Thm_PI_OddDualWeyl_Red_genM_map
import Theorems.Thm_PI_OddDualWeyl_Red_cM_map
import Theorems.Thm_PI_OddDualWeyl_Red_cM_mul
import Theorems.Thm_PI_OddDualWeyl_Red_map_mul_sbs
import Theorems.Thm_PI_OddDualWeyl_Red_rowAct_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
noncomputable section
open PI PI.OddDualWeyl PI.OddDualWeyl.Red
variable {R : Type*} [CommRing R] {k : ℕ}
namespace PI.OddDualWeyl.Red
theorem _root_.solution (A B : Matrix (Fin k) (Fin k) R) (p : MvPolynomial (Fin k × Fin k) R) :
    rowAct R A (rowAct R B p) = rowAct R (B * A) p := by
  rw [rowAct_eq, rowAct_eq, rowAct_eq, sbs_sbs,
    map_mul_sbs, cM_map, genM_map, cM_mul, Matrix.mul_assoc]
end PI.OddDualWeyl.Red
