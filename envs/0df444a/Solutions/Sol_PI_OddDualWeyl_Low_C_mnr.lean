-- Prove2me | solution 1 for PI.OddDualWeyl.Low.C_mnr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:04:45.06021+00:00
-- url     : https://prove2.me/submissions/b55d30b7-731e-4051-b49f-1198f183fe5d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_MnrUpdateEqZero

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
open PI PI.OddDualWeyl PI.OddDualWeyl.Low
variable {R : Type*} [CommRing R]
namespace PI.OddDualWeyl.Low
theorem _root_.solution {k n : ℕ} (h : n ≤ k) (ρ : Fin n → Fin k) :
    (Polynomial.C (mnr R h ρ) : Polynomial (MvPolynomial (Fin k × Fin k) R)) =
      (Matrix.of fun p q : Fin n =>
        Polynomial.C (X (ρ p, Fin.castLE h q) : MvPolynomial (Fin k × Fin k) R)).det := by
  rw [mnr, RingHom.map_det]
  congr 1
end PI.OddDualWeyl.Low
