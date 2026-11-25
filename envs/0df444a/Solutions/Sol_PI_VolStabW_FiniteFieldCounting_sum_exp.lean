-- Prove2me | solution 1 for PI.VolStabW.FiniteFieldCounting.sum_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:56:52.835487+00:00
-- url     : https://prove2.me/submissions/e5e2432f-2711-4758-abc7-bbb3fbdc46e5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensFFS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensFFT

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open PI.VolStabW.FiniteFieldCounting
namespace PI.VolStabW.FiniteFieldCounting
theorem _root_.solution (M : ℕ) : ∀ a, a ≤ M →
    ∑ j ∈ Finset.range a, (2 * (M - j) - 1) = 2 * M * a - a ^ 2 := by
  intro a
  induction a with
  | zero => intro _; simp
  | succ a ih =>
    intro ha
    rw [Finset.sum_range_succ, ih (by omega)]
    have h1 : a ^ 2 ≤ 2 * M * a := by nlinarith
    have h2 : (a + 1) ^ 2 ≤ 2 * M * (a + 1) := by nlinarith
    have h3 : a ≤ M := by omega
    have h4 : 1 ≤ 2 * (M - a) := by omega
    zify [h1, h2, h3, h4]
    ring
end PI.VolStabW.FiniteFieldCounting
