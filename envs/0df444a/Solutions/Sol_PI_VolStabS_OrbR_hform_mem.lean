-- Prove2me | solution 1 for PI.VolStabS.OrbR.hform_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:50:53.478582+00:00
-- url     : https://prove2.me/submissions/4427ce89-e01b-4dc1-b7e9-fb547a3a7c3b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_HformEntry
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_OrbRing
import Theorems.Thm_PI_VolStabS_OrbR_hform_mulVec

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
theorem _root_.solution (g : GL (Fin n) S) (hg : g ∈ UJ s J) (z w : Fin n → S) :
    hform s J ((g : Matrix (Fin n) (Fin n) S) *ᵥ z) ((g : Matrix (Fin n) (Fin n) S) *ᵥ w) =
      hform s J z w := by
  rw [hform_mulVec]
  rw [show cT s (g : Matrix (Fin n) (Fin n) S) * J * (g : Matrix (Fin n) (Fin n) S) = J from hg]
end PI.VolStabS.OrbR
