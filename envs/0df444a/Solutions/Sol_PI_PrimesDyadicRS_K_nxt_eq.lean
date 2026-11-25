-- Prove2me | solution 1 for PI.PrimesDyadicRS.K.nxt_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:17:27.498596+00:00
-- url     : https://prove2.me/submissions/e115c348-20c5-4df6-8e9c-929ab2795999

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_ThetaDiff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_SmallLoop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_Run1
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_Run2
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_Run3
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_Run4
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_SmallNaturalNumbersBound
import Theorems.Thm_PI_PrimesDyadicRS_K_pr_eq
import Theorems.Thm_PI_PrimesDyadicRS_K_pc_succ

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
theorem _root_.solution {Q h : ℕ} (hQ : Q = Nat.factorial 362) (h2 : 2 ≤ h) (hh : h < 131072) :
    nxt Q h (D h) = D (h + 1) := by
  have hA := pr_eq (m := h + 1) hQ (by omega) (by omega)
  have hs := pc_succ h
  unfold nxt D
  rw [hA, hs]
  by_cases he : (h + 1) % 2 = 0
  · have hq : (h + 1) / 2 = h / 2 + 1 := by omega
    have hB := pr_eq (m := (h + 1) / 2) hQ (by omega) (by omega)
    have hs2 := pc_succ (h / 2)
    have hmono : Nat.primeCounting (h / 2 + 1) ≤ Nat.primeCounting h :=
      Nat.monotone_primeCounting (by omega)
    rw [if_pos he, hB, hq, hs2]
    rw [hs2] at hmono
    split_ifs at hmono ⊢ <;> omega
  · have hq : (h + 1) / 2 = h / 2 := by omega
    have hmono : Nat.primeCounting (h / 2) ≤ Nat.primeCounting h :=
      Nat.monotone_primeCounting (by omega)
    rw [if_neg he, hq]
    split_ifs <;> omega
end PI.PrimesDyadicRS.K
