-- Prove2me | solution 1 for PI.VolStabS.FiniteFieldCounting.sum_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:50:23.185129+00:00
-- url     : https://prove2.me/submissions/3070cd1d-f54a-492a-bc62-dedc6ae0085f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensFFS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensFFT

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabS
open PI.VolStabS.FiniteFieldCounting
namespace PI.VolStabS.FiniteFieldCounting
theorem _root_.solution (M : ℕ) : ∀ a, a ≤ M →
    ∑ j ∈ Finset.range a, (2 * (M - j) - 1) = 2 * M * a - a ^ 2 := by
  intro a
  induction a with
  | zero => intro _; simp
  | succ a ih =>
    intro ha
    rw [Finset.sum_range_succ, ih (by omega)]
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le ha
    have e1 : a + 1 + d - a = d + 1 := by omega
    rw [e1]
    have e2 : 2 * (a + 1 + d) * a - a ^ 2 = a ^ 2 + 2 * a * (d + 1) := by
      apply Nat.sub_eq_of_eq_add
      ring
    have e3 : 2 * (a + 1 + d) * (a + 1) - (a + 1) ^ 2 = (a + 1) ^ 2 + 2 * (a + 1) * d := by
      apply Nat.sub_eq_of_eq_add
      ring
    rw [e2, e3]
    have e4 : 2 * (d + 1) - 1 = 2 * d + 1 := by omega
    rw [e4]
    ring
end PI.VolStabS.FiniteFieldCounting
