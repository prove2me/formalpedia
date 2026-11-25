-- Prove2me | solution 1 for PIW.AdelicOrbitU.hform_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:21:53.116912+00:00
-- url     : https://prove2.me/submissions/271af7c6-3584-4671-bf56-f24957808ca0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_UnitChoice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_HformEntry

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.AdelicOrbitU
open Matrix Formalism.UG
variable {S : Type} [CommRing S] (s : S →+* S) {n : ℕ} (J : Matrix (Fin n) (Fin n) S)
namespace PIW.AdelicOrbitU
theorem _root_.solution (i j : Fin n) :
    hform s J (Pi.single i 1) (Pi.single j 1) = J i j := by
  have hs : ∀ k, s ((Pi.single i (1 : S) : Fin n → S) k) = (Pi.single i (1 : S) : Fin n → S) k := fun k => by
    by_cases h : k = i
    · subst h
      simp
    · simp [h]
  unfold hform
  simp only [hs]
  simp [Pi.single_apply]
end PIW.AdelicOrbitU
