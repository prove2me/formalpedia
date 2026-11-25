-- Prove2me | solution 1 for PI.VolStabSW.OrbR.reflection_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:53:39.267822+00:00
-- url     : https://prove2.me/submissions/62ef8c65-f065-44c1-912f-832a78036e03

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
theorem _root_.solution (c : S) (u v z : Fin n → S) :
    r1 s J c u v *ᵥ z = z - (c * hform s J u z) • v := by
  unfold r1
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  congr 1
  ext k
  simp only [hform, Matrix.mulVec, dotProduct, vecMulVec, vecMul, Matrix.smul_apply,
    Matrix.of_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring
end PI.VolStabSW.OrbR
