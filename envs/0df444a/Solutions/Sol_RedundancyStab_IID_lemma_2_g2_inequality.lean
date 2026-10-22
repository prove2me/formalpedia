-- Prove2me | solution 1 for RedundancyStab.IID.lemma_2_g2_inequality
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T09:08:57.542639+00:00
-- url     : https://prove2.me/submissions/137dbd11-81c5-48cf-a335-d50ed11d7ff8

import Mathlib
import Definitions.Def_RedundancyStab_IID_Model

open RedundancyStab.IID

theorem solution (K d : ℕ) (hd : 1 ≤ d) (hdK : d ≤ K) (n : JobType K d → ℝ)
    (hn : ∀ c, 0 ≤ n c) (hne : n ≠ 0) (s : Fin K)
    (hs : ∀ l, fluidCopies K d n l ≤ fluidCopies K d n s) :
    (d : ℝ) ≤ ∑ c ∈ typesAt K d s, ∑ l ∈ c.1, n c / fluidCopies K d n l := by
  classical
  -- a type is counted at each of its servers
  have hle : ∀ (c : JobType K d) (l : Fin K), l ∈ c.1 → n c ≤ fluidCopies K d n l := by
    intro c l hl
    unfold fluidCopies
    exact Finset.single_le_sum (fun c' _ => hn c')
      (by simp [typesAt, hl])
  -- m_s > 0
  have hms : 0 < fluidCopies K d n s := by
    obtain ⟨c, hc⟩ : ∃ c, n c ≠ 0 := by
      by_contra h; push_neg at h; exact hne (funext h)
    have hcpos : 0 < n c := lt_of_le_of_ne (hn c) (Ne.symm hc)
    have hne' : c.1.Nonempty := by
      rw [← Finset.card_pos, c.2]; omega
    obtain ⟨l, hl⟩ := hne'
    exact lt_of_lt_of_le hcpos ((hle c l hl).trans (hs l))
  have step : ∀ c ∈ typesAt K d s, (d : ℝ) * (n c / fluidCopies K d n s) ≤
      ∑ l ∈ c.1, n c / fluidCopies K d n l := by
    intro c _
    have : ∑ l ∈ c.1, n c / fluidCopies K d n s ≤ ∑ l ∈ c.1, n c / fluidCopies K d n l := by
      apply Finset.sum_le_sum
      intro l hl
      by_cases hml : fluidCopies K d n l = 0
      · have h0 : n c = 0 := le_antisymm (hml ▸ hle c l hl) (hn c)
        simp [h0]
      · have hmlpos : 0 < fluidCopies K d n l :=
          lt_of_le_of_ne ((hn c).trans (hle c l hl)) (Ne.symm hml)
        exact div_le_div_of_nonneg_left (hn c) hmlpos (hs l)
    simpa [Finset.sum_const, c.2, nsmul_eq_mul] using this
  calc (d : ℝ) = (d : ℝ) * (fluidCopies K d n s / fluidCopies K d n s) := by
        rw [div_self hms.ne', mul_one]
    _ = ∑ c ∈ typesAt K d s, (d : ℝ) * (n c / fluidCopies K d n s) := by
        rw [← Finset.mul_sum, ← Finset.sum_div]; rfl
    _ ≤ _ := Finset.sum_le_sum step
