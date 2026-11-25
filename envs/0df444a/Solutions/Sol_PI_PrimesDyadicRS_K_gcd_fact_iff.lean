-- Prove2me | solution 1 for PI.PrimesDyadicRS.K.gcd_fact_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:04:36.297408+00:00
-- url     : https://prove2.me/submissions/9c64782a-3827-4f98-8b05-41e4f351b471

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_ThetaDiff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_SmallLoop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_Run1
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_Run2
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_Run3
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_Run4
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_SmallNaturalNumbersBound

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
theorem _root_.solution {m k : ℕ} (h2 : 2 ≤ m) (hk : k < m) (hm : m < (k + 1) ^ 2) :
    Nat.gcd m k.factorial = 1 ↔ m.Prime := by
  constructor
  · intro hg
    by_contra hp
    have hmf := Nat.minFac_sq_le_self (by omega) hp
    have hle : m.minFac ≤ k := by
      by_contra hc
      push Not at hc
      have : (k + 1) ^ 2 ≤ m.minFac ^ 2 := Nat.pow_le_pow_left hc 2
      omega
    have hd : m.minFac ∣ Nat.gcd m k.factorial :=
      Nat.dvd_gcd (Nat.minFac_dvd m) (Nat.dvd_factorial (Nat.minFac_pos m) hle)
    rw [hg, Nat.dvd_one, Nat.minFac_eq_one_iff] at hd
    omega
  · intro hp
    exact (Nat.Prime.coprime_iff_not_dvd hp).2 fun hd => by
      have := (Nat.Prime.dvd_factorial hp).1 hd
      omega
end PI.PrimesDyadicRS.K
