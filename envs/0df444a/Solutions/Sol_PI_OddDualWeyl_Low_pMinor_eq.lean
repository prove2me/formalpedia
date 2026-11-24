-- Prove2me | solution 1 for PI.OddDualWeyl.Low.pMinor_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:24:46.445441+00:00
-- url     : https://prove2.me/submissions/e67f1f37-ea26-45cc-92b0-00e4c78bdbc8

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
theorem _root_.solution {k : ℕ} (σ : Equiv.Perm (Fin k)) (n : ℕ) (h : n ≤ k) :
    pMinor R σ n h = mnr R h (σ ∘ Fin.castLE h) := rfl
end PI.OddDualWeyl.Low
