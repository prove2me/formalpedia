-- Prove2me | solution 1 for PI.VolStabW.OrbR.gram_tM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:04:09.032967+00:00
-- url     : https://prove2.me/submissions/554ec2ba-c58f-4f03-9206-bf71d4ca555c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_HformEntry
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_OrbRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW PI.VolStabW.OrbR
open Matrix Formalism.UG PIW.AdelicOrbitU
variable {S : Type} [CommRing S] (s : S →+* S) {n : ℕ} (J : Matrix (Fin n) (Fin n) S)
namespace PI.VolStabW.OrbR
theorem _root_.solution {m : ℕ} (X : Fin m → Fin n → S) (i j : Fin m) :
    hform s J (X i) (X j) = (cT s (tM X) * J * tM X) i j := by
  simp only [hform, cT, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, tM, Matrix.of_apply,
    Finset.sum_mul]
  exact Finset.sum_comm
end PI.VolStabW.OrbR
