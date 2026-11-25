-- Prove2me | solution 1 for PI.SqfPrimeFactor.W.ana_three
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:24:11.238401+00:00
-- url     : https://prove2.me/submissions/da973838-8264-433f-b912-dea8e92472e3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PrimesDyadicRS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreePrimeFactor_AnaCore

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.SqfPrimeFactor PI.SqfPrimeFactor.W
open Finset
namespace PI.SqfPrimeFactor.W
theorem _root_.solution (r : ℕ) (hr : 100 ≤ r) :
    (({r - 2, r - 1, r} : Finset ℕ).filter Nat.Prime).card ≤ 2 := by
  obtain ⟨e, he, hev, he4⟩ : ∃ e ∈ ({r - 2, r - 1, r} : Finset ℕ), Even e ∧ 4 ≤ e := by
    rcases Nat.even_or_odd r with h | h
    · exact ⟨r, by simp, h, by omega⟩
    · refine ⟨r - 1, by simp, ?_, by omega⟩
      obtain ⟨k, hk⟩ := h
      exact ⟨k, by omega⟩
  have hsub : ({r - 2, r - 1, r} : Finset ℕ).filter Nat.Prime ⊆
      ({r - 2, r - 1, r} : Finset ℕ).erase e := by
    intro x hx
    rw [mem_filter] at hx
    rw [mem_erase]
    refine ⟨?_, hx.1⟩
    rintro rfl
    have := hx.2.eq_one_or_self_of_dvd 2 (even_iff_two_dvd.1 hev)
    omega
  calc _ ≤ _ := card_le_card hsub
    _ = _ := card_erase_of_mem he
    _ ≤ 3 - 1 := Nat.sub_le_sub_right card_le_three 1
end PI.SqfPrimeFactor.W
