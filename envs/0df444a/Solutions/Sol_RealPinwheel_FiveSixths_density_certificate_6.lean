-- Prove2me | solution 1 for RealPinwheel.FiveSixths.density_certificate_6
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:55:57.876693+00:00
-- url     : https://prove2.me/submissions/ef689978-e1eb-43e5-a47a-ba3dbe98cbf6

import Theorems.Thm_RealPinwheel_FiveSixths_initial_atoms_sound
import Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_D6_0014
import Theorems.Thm_RealPinwheel_FiveSixths_words_valid_D6_000
open RealPinwheel.FiveSixths

theorem solution (A : Instance 6) (hD : density A ≤ (5 : ℝ) / 6) :
    ∃ (L : ℕ) (S : ℕ → Fin 6), 0 < L ∧ L ≤ 64 ∧
      (∀ t, S (t + L) = S t) ∧ Valid A.period S := by
  let d : Fin 6 → ℝ := fun i => 1 / A.period i
  have ha : ∀ i, 0 < A.period i := fun i => lt_of_lt_of_le (by norm_num) (A.one_le i)
  have hpos : ∀ i, 0 < d i := fun i => one_div_pos.mpr (ha i)
  have hord : Antitone d := by
    intro i j hij
    exact one_div_le_one_div_of_le (ha i) (A.ordered hij)
  have hsum : (∑ i, if i.val < 6 then d i else 0) ≤ (5 : ℝ) / 6 := by
    simpa [density, d, Fin.sum_univ_succ, add_assoc] using hD
  obtain ⟨j, hb⟩ := RealPinwheel.FiveSixths.covered_fragment_D6_0014 d (initial_atoms_sound d hpos hord hsum)
  exact RealPinwheel.FiveSixths.words_valid_D6_000 A j (by omega) (by omega) hb
