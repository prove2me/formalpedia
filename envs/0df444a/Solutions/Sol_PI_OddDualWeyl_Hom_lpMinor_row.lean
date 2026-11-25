-- Prove2me | solution 1 for PI.OddDualWeyl.Hom.lpMinor_row
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:58:35.378576+00:00
-- url     : https://prove2.me/submissions/b909d6f1-c5db-4cd4-b14f-e6dc94800aab

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
theorem _root_.solution (s : ℕ) (hr : s ≤ k) (hn : s ≤ k) (c : Fin k) :
    IsWeightedHomogeneous (rowW c) (lpMinor R s hr hn)
      (∑ p : Fin s, if Fin.castLE hr p = c then 1 else 0) := by
  unfold lpMinor
  apply det_isWH
  intro p q
  simp only [Matrix.of_apply]
  convert isWeightedHomogeneous_X R (rowW c) (Fin.castLE hr p, Fin.castLE hn q) using 1
  simp [rowW]
end PI.OddDualWeyl.Hom
