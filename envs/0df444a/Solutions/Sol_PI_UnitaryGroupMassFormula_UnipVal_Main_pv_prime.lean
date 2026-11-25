-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnipVal.Main.pv_prime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:48:01.151955+00:00
-- url     : https://prove2.me/submissions/8af03b3c-2cd8-4233-8432-52fbd97fa8d9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnipVal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentValuation_VwIntEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnipVal PI.UnitaryGroupMassFormula.UnipVal.Main
open PI.UnipVal
variable {K : Type} [Field K] [NumberField K]
namespace PI.UnitaryGroupMassFormula.UnipVal.Main
theorem _root_.solution (l g : ℕ) (hl : l.Prime) (hg : g.Prime) :
    padicValNat l g = if l = g then 1 else 0 := by
  haveI : Fact l.Prime := ⟨hl⟩
  split_ifs with h
  · rw [h]
    exact padicValNat.self hg.one_lt
  · exact padicValNat.eq_zero_of_not_dvd fun hd => h ((Nat.prime_dvd_prime_iff_eq hl hg).mp hd)
end PI.UnitaryGroupMassFormula.UnipVal.Main
