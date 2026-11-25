-- Prove2me | solution 1 for PI.PrimesDyadicRS.K.loop_sound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:22:12.897159+00:00
-- url     : https://prove2.me/submissions/de59d4bf-c6a8-47ab-b708-d42ddeb11540

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_ThetaDiff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_SmallLoop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_Run1
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_Run2
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_Run3
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_Run4
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_SmallNaturalNumbersBound
import Theorems.Thm_PI_PrimesDyadicRS_K_nxt_eq
import Theorems.Thm_PI_PrimesDyadicRS_K_force_eq


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
theorem _root_.solution {Q hT dT : ℕ} (hQ : Q = Nat.factorial 362) :
    ∀ k h d : ℕ, loop Q hT dT k h d = true → 2 ≤ h → h + k ≤ 131072 → d = D h →
      (hT = h + k ∧ dT = D hT) ∧ ∀ m, h ≤ m → m < h + k → 41 ≤ m → tstR m (D m) = true := by
  intro k
  induction k with
  | zero =>
    intro h d hl _ _ hd
    simp only [loop, Bool.and_eq_true, beq_iff_eq] at hl
    obtain ⟨e1, e2⟩ := hl
    subst e1 e2 hd
    exact ⟨⟨rfl, rfl⟩, fun m h1 h2 _ => by omega⟩
  | succ k ih =>
    intro h d hl h2 hk hd
    rw [loop, force_eq, force_eq, Bool.and_eq_true] at hl
    obtain ⟨ht, hl⟩ := hl
    subst hd
    rw [nxt_eq hQ h2 (by omega)] at hl
    obtain ⟨⟨e1, e2⟩, hall⟩ := ih (h + 1) (D (h + 1)) hl (by omega) (by omega) rfl
    refine ⟨⟨by omega, e2⟩, fun m hm1 hm2 hm3 => ?_⟩
    rcases Nat.eq_or_lt_of_le hm1 with rfl | hlt
    · rw [Bool.or_eq_true, Nat.blt_eq] at ht
      rcases ht with ht | ht
      · omega
      · exact ht
    · exact hall m hlt (by omega) hm3
end PI.PrimesDyadicRS.K
