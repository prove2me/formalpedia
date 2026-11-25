-- Prove2me | solution 1 for PI.PrimesDyadicRS.K.small_natural_numbers_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:39:19.127741+00:00
-- url     : https://prove2.me/submissions/0c28230c-4401-4789-8c27-27cf3dbd2fd2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_ThetaDiff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_SmallLoop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_Run1
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_Run2
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_Run3
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_Run4
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_SmallNaturalNumbersBound
import Theorems.Thm_PI_PrimesDyadicRS_K_tstR_sound
import Theorems.Thm_PI_PrimesDyadicRS_K_tests

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.PrimesDyadicRS PI.PrimesDyadicRS.K
open Real
namespace PI.PrimesDyadicRS.K
theorem _root_.solution : PI.PrimesDyadicRS.W.SmallNat := by
  intro h h1 h2
  have ht := tstR_sound (tests h h1 h2) (by omega)
  have hmono : Nat.primeCounting (h / 2) ≤ Nat.primeCounting h :=
    Nat.monotone_primeCounting (Nat.div_le_self h 2)
  have hc : ((D h : ℕ) : ℝ) = (Nat.primeCounting h : ℝ) - (Nat.primeCounting (h / 2) : ℝ) := by
    rw [D, Nat.cast_sub hmono]
  rw [hc] at ht
  exact ht
end PI.PrimesDyadicRS.K
