-- Prove2me | solution 1 for SchedComplexity.NoWait.iota_exists
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T11:44:45.981306+00:00
-- url     : https://prove2.me/submissions/e84aad7e-2568-46bc-b204-f19b04dfae61

import Mathlib
import Definitions.Def_SchedComplexity_NoWait_Construction



namespace SchedComplexity.NoWait

def ioT (n j k : ℕ) : ℕ := if j < k then k - j - 1 else k + n - j - 1

def ioF (n : ℕ) (j k : Fin n) : ℕ := 2 + j.val * (n - 1) + ioT n j.val k.val

theorem io_core (n : ℕ) (hn : n ≠ 2) : ∃ ι : Fin n → Fin n → ℕ, Admissible n ι := by
  refine ⟨ioF n, ?_, ?_, ?_, ?_⟩
  · intro j k hjk
    have hj := j.isLt
    have hk := k.isLt
    have hne : j.val ≠ k.val := fun h => hjk (Fin.ext h)
    unfold ioF ioT
    have h1 : (j.val + 1) * (n - 1) ≤ n * (n - 1) := Nat.mul_le_mul_right _ (by omega)
    have h2 : (j.val + 1) * (n - 1) = j.val * (n - 1) + (n - 1) := by ring
    split_ifs <;> omega
  · intro j k j' k' hjk hjk' h
    have hj := j.isLt
    have hk := k.isLt
    have hj' := j'.isLt
    have hk' := k'.isLt
    have hne : j.val ≠ k.val := fun h => hjk (Fin.ext h)
    have hne' : j'.val ≠ k'.val := fun h => hjk' (Fin.ext h)
    unfold ioF ioT at h
    have hjj : j.val = j'.val := by
      by_contra hc
      rcases Nat.lt_or_gt_of_ne hc with hlt | hlt
      · have : (j.val + 1) * (n - 1) ≤ j'.val * (n - 1) := Nat.mul_le_mul_right _ hlt
        have h2 : (j.val + 1) * (n - 1) = j.val * (n - 1) + (n - 1) := by ring
        split_ifs at h <;> omega
      · have : (j'.val + 1) * (n - 1) ≤ j.val * (n - 1) := Nat.mul_le_mul_right _ hlt
        have h2 : (j'.val + 1) * (n - 1) = j'.val * (n - 1) + (n - 1) := by ring
        split_ifs at h <;> omega
    have hjj' : j = j' := Fin.ext hjj
    refine ⟨hjj', ?_⟩
    rw [hjj] at h
    have : k.val = k'.val := by split_ifs at h <;> omega
    exact Fin.ext this
  · intro i hi1 hi2
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0; simp at hi2; omega
    have hdm := Nat.div_add_mod (i - 2) (n - 1)
    have hr : (i - 2) % (n - 1) < n - 1 := by
      apply Nat.mod_lt; by_contra hc
      have : n - 1 = 0 := by omega
      rw [this] at hi2; simp at hi2; omega
    set j := (i - 2) / (n - 1) with hjdef
    set r := (i - 2) % (n - 1) with hrdef
    have hjn : j < n := by
      by_contra hc
      have : (n - 1) * n ≤ (n - 1) * j := Nat.mul_le_mul_left _ (by omega)
      have h5 : n * (n - 1) = (n - 1) * n := by ring
      omega
    have hmul : j * (n - 1) = (n - 1) * j := by ring
    by_cases hc : j + 1 + r < n
    · refine ⟨⟨j, hjn⟩, ⟨j + 1 + r, hc⟩, ?_, ?_⟩
      · intro h; have := congrArg Fin.val h; simp at this; omega
      · unfold ioF ioT; simp
        split_ifs <;> omega
    · refine ⟨⟨j, hjn⟩, ⟨j + 1 + r - n, by omega⟩, ?_, ?_⟩
      · intro h; have := congrArg Fin.val h; simp at this; omega
      · unfold ioF ioT; simp
        split_ifs <;> omega
  · intro j l k hjl hlk
    have hj := j.isLt
    have hl := l.isLt
    have hk := k.isLt
    have hne : j.val ≠ l.val := fun h => hjl (Fin.ext h)
    have hne' : l.val ≠ k.val := fun h => hlk (Fin.ext h)
    intro h
    unfold ioF ioT at h
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have : (j.val + 1) * (n - 1) ≤ l.val * (n - 1) := Nat.mul_le_mul_right _ hlt
      have h2 : (j.val + 1) * (n - 1) = j.val * (n - 1) + (n - 1) := by ring
      split_ifs at h <;> omega
    · have : (l.val + 1) * (n - 1) ≤ j.val * (n - 1) := Nat.mul_le_mul_right _ hlt
      have h2 : (l.val + 1) * (n - 1) = l.val * (n - 1) + (n - 1) := by ring
      have h3 : j.val = l.val + 1 ∨ l.val + 1 < j.val := by omega
      rcases h3 with h3 | h3
      · rw [h3] at h
        split_ifs at h <;> omega
      · have : (l.val + 2) * (n - 1) ≤ j.val * (n - 1) := Nat.mul_le_mul_right _ h3
        have h2 : (l.val + 2) * (n - 1) = l.val * (n - 1) + 2 * (n - 1) := by ring
        split_ifs at h <;> omega

end SchedComplexity.NoWait

open SchedComplexity.NoWait


theorem solution (n : ℕ) (hn : n ≠ 2) : ∃ ι : Fin n → Fin n → ℕ, Admissible n ι := by
  exact io_core n hn
