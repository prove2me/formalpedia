-- Prove2me | solution 1 for TenChallenges.challenge_03_r1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:17:36.593834+00:00
-- url     : https://prove2.me/submissions/c34bbc86-3d76-4b50-a5bc-e7fc07ee7f07

import Definitions.Def_TenChallenges_Challenge_03
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.Data.Fintype.Pigeonhole

open Function

theorem solution : TenChallenges.statement_03 1 := by
  classical
  intro _ V _ _ G hloop hdeg
  have hnext (v : V) : ∃ w, G.Adj v w := by
    exact (Set.ncard_pos (Set.toFinite _)).mp (hdeg v)
  choose f hf using hnext
  let z : V := Classical.arbitrary V
  obtain ⟨a, b, heq, hne⟩ : ∃ a b : ℕ, f^[a] z = f^[b] z ∧ a ≠ b := by
    simpa [Function.Injective] using not_injective_infinite_finite (f^[·] z)
  have hrepeat : ∃ m n : ℕ, m < n ∧ f^[n] z = f^[m] z := by
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨a, b, h, heq.symm⟩
    · exact ⟨b, a, h, heq⟩
  obtain ⟨m, n, hmn, heq⟩ := hrepeat
  let x := f^[m] z
  have hp : IsPeriodicPt f (n - m) x := by
    change f^[n - m] (f^[m] z) = f^[m] z
    rw [← iterate_add_apply, Nat.sub_add_cancel hmn.le]
    exact heq
  have hpos : 0 < minimalPeriod f x := hp.minimalPeriod_pos (Nat.sub_pos_of_lt hmn)
  have hnotone : minimalPeriod f x ≠ 1 := by
    intro h
    have hfix : f x = x := minimalPeriod_eq_one_iff_isFixedPt.mp h
    exact hloop x (by simpa only [hfix] using hf x)
  refine ⟨minimalPeriod f x, by omega, ?_, ?_⟩
  · have hbound : minimalPeriod f x ≤ Fintype.card V := minimalPeriod_le_card
    omega
  · refine ⟨fun i => f^[i.val] x, ?_, ?_⟩
    · intro i j hij
      apply Fin.ext
      exact (iterate_eq_iterate_iff_of_lt_minimalPeriod i.isLt j.isLt).mp hij
    · intro i
      have hstep : f^[((finRotate (minimalPeriod f x) i).val)] x = f (f^[i.val] x) := by
        letI : NeZero (minimalPeriod f x) := ⟨Nat.ne_of_gt hpos⟩
        rw [finRotate_apply]
        rw [Fin.val_add]
        change f^[(i.val + (1 % minimalPeriod f x)) % minimalPeriod f x] x = f (f^[i.val] x)
        rw [Nat.add_mod_mod]
        rw [iterate_mod_minimalPeriod_eq, iterate_succ_apply']
      dsimp only
      rw [hstep]
      exact hf _
