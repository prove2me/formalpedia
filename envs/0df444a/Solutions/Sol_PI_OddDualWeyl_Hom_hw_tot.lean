-- Prove2me | solution 1 for PI.OddDualWeyl.Hom.hw_tot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:06:00.778098+00:00
-- url     : https://prove2.me/submissions/27ed8ca7-b117-4ef9-a050-9bb73406a83d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_HighestWeightMultiplicity
import Theorems.Thm_PI_OddDualWeyl_Hom_lpMinor_tot

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
theorem _root_.solution (ν : Fin k → ℕ) : IsHomogeneous (hw R (le_refl k) ν) (degW ν) := by
  unfold hw degW
  apply IsHomogeneous.prod
  intro s _
  have h0 : IsHomogeneous (lpMinor R (s.val + 1) (by omega) (by omega) : MvPolynomial (Fin k × Fin k) R)
      (s.val + 1) := lpMinor_tot _ _ _
  convert h0.pow (ν s - nuNext ν s) using 1 <;> exact Nat.mul_comm _ _
end PI.OddDualWeyl.Hom
