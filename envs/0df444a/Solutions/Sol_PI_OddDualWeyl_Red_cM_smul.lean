-- Prove2me | solution 1 for PI.OddDualWeyl.Red.cM_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:59:31.684208+00:00
-- url     : https://prove2.me/submissions/c89734e0-725f-4b3a-ba6b-dec2f702d041

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_AevalMulHomog

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
variable {K : Type*} [Field K] {k : ℕ}
namespace PI.OddDualWeyl.Red
theorem _root_.solution (c : K) (g : Matrix (Fin k) (Fin k) K) : cM (c • g) = (C c : MvPolynomial (Fin k × Fin k) K) • cM g := by
  ext i j
  simp [cM, smul_eq_mul]
end PI.OddDualWeyl.Red
