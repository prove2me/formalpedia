-- Prove2me | solution 1 for PI.OddDualWeyl.Jac.det_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:59:02.697942+00:00
-- url     : https://prove2.me/submissions/54ae3cc7-c6e5-4b92-a347-451545d89fd5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacobiMinorIdentity

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
open PI PI.OddDualWeyl PI.OddDualWeyl.Jac
namespace PI.OddDualWeyl.Jac
theorem _root_.solution {R : Type*} [CommRing R] {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (eI eJ : ι ≃ Fin k) (A : Matrix (Fin k) (Fin k) R) :
    (A.submatrix eI eJ).det = ((Equiv.Perm.sign (eJ.trans eI.symm) : ℤ) : R) * A.det := by
  have h1 : A.submatrix eI eJ = (A.submatrix eI eI).submatrix id (eJ.trans eI.symm) := by
    ext i j
    simp
  rw [h1]
  rw [det_permute', det_submatrix_equiv_self]
end PI.OddDualWeyl.Jac
