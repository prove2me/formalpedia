-- Prove2me | solution 1 for PI.VolStabSW.OrbR.hform_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:53:28.598644+00:00
-- url     : https://prove2.me/submissions/7f2cc8ce-d938-485f-af34-6f2d8cb3dc74

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_HformEntry
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_OrbRing
import Theorems.Thm_PI_VolStabSW_OrbR_hform_mulVec

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
theorem _root_.solution (g : GL (Fin n) S) (hg : g ∈ UJ s J) (z w : Fin n → S) :
    hform s J ((g : Matrix (Fin n) (Fin n) S) *ᵥ z) ((g : Matrix (Fin n) (Fin n) S) *ᵥ w) =
      hform s J z w := by
  rw [hform_mulVec]
  have hg' : cT s (g : Matrix (Fin n) (Fin n) S) * J * (g : Matrix (Fin n) (Fin n) S) = J := hg
  rw [hg']
end PI.VolStabSW.OrbR
