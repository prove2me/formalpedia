-- Prove2me | solution 1 for PI.VolStabW.OrbR.gram_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:58:49.644197+00:00
-- url     : https://prove2.me/submissions/b5bd6a22-2dfe-48d8-b2d3-b85d5ff766cf

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
theorem _root_.solution {m k : ℕ} (N : Matrix (Fin n) (Fin m) S) (Q : Matrix (Fin m) (Fin k) S) :
    cT s (N * Q) * J * (N * Q) = cT s Q * (cT s N * J * N) * Q := by
  rw [cT_mul]; simp only [Matrix.mul_assoc]
end PI.VolStabW.OrbR
