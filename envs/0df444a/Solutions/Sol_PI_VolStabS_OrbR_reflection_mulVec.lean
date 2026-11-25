-- Prove2me | solution 1 for PI.VolStabS.OrbR.reflection_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:51:08.544643+00:00
-- url     : https://prove2.me/submissions/878b4b1a-d244-41c8-8233-f1b5b766ec4e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_HformEntry
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_OrbRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabS PI.VolStabS.OrbR
open Matrix Formalism.UG PIW.AdelicOrbitU
variable {S : Type} [CommRing S] (s : S →+* S) {n : ℕ} (J : Matrix (Fin n) (Fin n) S)
namespace PI.VolStabS.OrbR
theorem _root_.solution (c : S) (u v z : Fin n → S) :
    r1 s J c u v *ᵥ z = z - (c * hform s J u z) • v := by
  have hf : hform s J u z = (fun i => s (u i)) ⬝ᵥ (J *ᵥ z) := by
    simp only [hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  rw [r1, Matrix.sub_mulVec, Matrix.one_mulVec, hf, Matrix.dotProduct_mulVec]
  ext i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Matrix.smul_apply,
    Matrix.vecMulVec_apply]
  congr 1
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring
end PI.VolStabS.OrbR
