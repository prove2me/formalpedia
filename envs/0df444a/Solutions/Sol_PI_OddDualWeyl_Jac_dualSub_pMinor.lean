-- Prove2me | solution 1 for PI.OddDualWeyl.Jac.dualSub_pMinor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:05:09.63183+00:00
-- url     : https://prove2.me/submissions/76b1de59-4331-43f5-95bf-687badcba4db

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
theorem _root_.solution (R : Type*) [CommRing R] {k : ℕ} (σ : Equiv.Perm (Fin k)) (s : ℕ)
    (hs : s ≤ k) :
    dualSub R k (pMinor R σ s hs) =
      (Matrix.of fun p q : Fin s =>
        adjugate (genM R k) (Fin.rev (Fin.castLE hs q)) (σ (Fin.castLE hs p))).det := by
  rw [PI.OddDualWeyl.dualSub, PI.OddDualWeyl.pMinor, AlgHom.map_det]
  exact congrArg Matrix.det (Matrix.ext fun p q => by simp [PI.OddDualWeyl.dualM])
end PI.OddDualWeyl.Jac
