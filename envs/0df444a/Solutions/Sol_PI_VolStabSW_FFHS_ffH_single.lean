-- Prove2me | solution 1 for PI.VolStabSW.FFHS.ffH_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:54:10.354804+00:00
-- url     : https://prove2.me/submissions/56c07552-0a98-4967-b432-656e1ad8fe80

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensFFCnt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensFFIn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW PI.VolStabSW.FFHS
open Module Polynomial
variable {K : Type} [Field K] {σ : K →+* K}
namespace PI.VolStabSW.FFHS
theorem _root_.solution {n : ℕ} (T : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    ffH σ T (Pi.single i 1) (Pi.single j 1) = T i j := by
  have hs : ∀ i' : Fin n, σ ((Pi.single i 1 : Fin n → K) i') = (Pi.single i 1 : Fin n → K) i' := by
    intro i'
    by_cases h : i' = i
    · subst h
      simp
    · simp [Pi.single_eq_of_ne h]
  simp only [PI.VolStabSW.ffH, hs]
  simp [Pi.single_apply]
end PI.VolStabSW.FFHS
