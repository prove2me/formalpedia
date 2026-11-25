-- Prove2me | solution 1 for PI.VolStabSW.OrbR.gram_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:54:58.164255+00:00
-- url     : https://prove2.me/submissions/0d398620-53bd-4c2f-a5b2-ff3db89fc4c7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_HformEntry
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_OrbRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW PI.VolStabSW.OrbR
open Matrix Formalism.UG PIW.AdelicOrbitU
variable {S : Type} [CommRing S] (s : S →+* S) {n : ℕ} (J : Matrix (Fin n) (Fin n) S)
namespace PI.VolStabSW.OrbR
theorem _root_.solution {m k : ℕ} (N : Matrix (Fin n) (Fin m) S) (Q : Matrix (Fin m) (Fin k) S) :
    cT s (N * Q) * J * (N * Q) = cT s Q * (cT s N * J * N) * Q := by
  unfold cT
  rw [Matrix.map_mul, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]
end PI.VolStabSW.OrbR
