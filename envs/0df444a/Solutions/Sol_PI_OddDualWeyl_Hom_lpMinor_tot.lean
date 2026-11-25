-- Prove2me | solution 1 for PI.OddDualWeyl.Hom.lpMinor_tot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:58:38.757751+00:00
-- url     : https://prove2.me/submissions/ca2ec682-1d17-4b7b-b998-0655275df278

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_HighestWeightMultiplicity
import Theorems.Thm_PI_OddDualWeyl_Hom_det_isWH

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
open PI PI.OddDualWeyl
open PI.OddDualWeyl.Hom
variable {R : Type} [CommRing R] {k : ℕ}
variable {wt : Fin k × Fin k → ℤ} {δ : ℤ}
namespace PI.OddDualWeyl.Hom
theorem _root_.solution (s : ℕ) (hr : s ≤ k) (hn : s ≤ k) :
    IsWeightedHomogeneous (1 : Fin k × Fin k → ℕ) (lpMinor R s hr hn) s := by
  have := det_isWH (w := (1 : Fin k × Fin k → ℕ))
    (Matrix.of fun p q : Fin s => (X (Fin.castLE hr p, Fin.castLE hn q) : MvPolynomial (Fin k × Fin k) R))
    (fun _ => 1)
    (fun p q => by simpa using isWeightedHomogeneous_X R (1 : Fin k × Fin k → ℕ) (Fin.castLE hr p, Fin.castLE hn q))
  simpa [lpMinor] using this
end PI.OddDualWeyl.Hom
