-- Prove2me | solution 1 for PI.VolStabW.OrbR.reflection_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:57:02.496849+00:00
-- url     : https://prove2.me/submissions/a3665bf8-ed9c-4226-b6d7-d9e8473a6718

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_HformEntry
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_OrbRing
import Theorems.Thm_PIW_AdelicOrbitU_hform_eq_dot


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
theorem _root_.solution (c : S) (u v z : Fin n → S) :
    r1 s J c u v *ᵥ z = z - (c * hform s J u z) • v := by
  rw [r1, sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec, ← dotProduct_mulVec,
    ← hform_eq_dot, op_smul_eq_smul, smul_smul]
end PI.VolStabW.OrbR
