-- Prove2me | solution 1 for RealPinwheel.FiveSixths.five_sixths_periodic
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T02:53:40.881204+00:00
-- url     : https://prove2.me/submissions/3d50e755-7a30-4823-ad05-378b5f4a410e

import Theorems.Thm_RealPinwheel_FiveSixths_bounded_density_base
import Theorems.Thm_RealPinwheel_FiveSixths_bounded_potential_base
import Theorems.Thm_RealPinwheel_FiveSixths_bounded_folding

open RealPinwheel.FiveSixths

private lemma potential_le_density {n : ℕ} (A : Instance n) : potential A ≤ density A := by
  apply Finset.sum_le_sum
  intro i _
  split_ifs
  · rfl
  · exact le_of_lt (one_div_pos.mpr (lt_of_lt_of_le (by norm_num) (A.one_le i)))

private lemma potential_periodic : ∀ (n : ℕ) (A : Instance n), 9 ≤ n →
    potential A ≤ (5 : ℝ) / 6 →
    ∃ (L : ℕ) (S : ℕ → Fin n), 0 < L ∧ L < 4 * 2 ^ n ∧
      (∀ t, S (t + L) = S t) ∧ Valid A.period S := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro A hn hP
    by_cases h9 : n = 9
    · subst n
      obtain ⟨L, S, hL, hb, hp, hv⟩ := bounded_potential_base A hP
      refine ⟨L, S, hL, ?_, hp, hv⟩
      norm_num at ⊢
      omega
    · obtain ⟨r, hrn⟩ := Nat.exists_eq_add_of_le (show 2 ≤ n by omega)
      have hn' : n = r + 2 := by omega
      clear hrn
      subst n
      have hr : 9 ≤ r + 1 := by omega
      obtain ⟨B, hBP, hB⟩ := bounded_folding A hr hP
      obtain ⟨L, S, hL, hb, hp, hv⟩ := ih (r + 1) (by omega) B hr hBP
      obtain ⟨T, hT, hvT⟩ := hB L S ⟨hL, hp⟩ hv
      refine ⟨2 * L, T, hT.1, ?_, hT.2, hvT⟩
      have he : 4 * 2 ^ (r + 2) = 2 * (4 * 2 ^ (r + 1)) := by
        rw [show r + 2 = (r + 1) + 1 by omega, pow_succ]
        ring
      rw [he]
      omega

theorem solution {n : ℕ} (A : Instance n)
    (hD : density A ≤ (5 : ℝ) / 6) :
    ∃ (L : ℕ) (S : ℕ → Fin n),
      0 < L ∧ L < 4 * 2 ^ n ∧
      (∀ t : ℕ, S (t + L) = S t) ∧ Valid A.period S := by
  by_cases hn : n ≤ 8
  · exact bounded_density_base A hn hD
  · exact potential_periodic n A (by omega) ((potential_le_density A).trans hD)
