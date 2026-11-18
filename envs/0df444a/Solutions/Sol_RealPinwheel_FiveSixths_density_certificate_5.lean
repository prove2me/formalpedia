-- Prove2me | solution 1 for RealPinwheel.FiveSixths.density_certificate_5
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:39:42.581912+00:00
-- url     : https://prove2.me/submissions/66c82def-b2a3-4546-a94c-78d2a3837368

import Theorems.Thm_RealPinwheel_FiveSixths_linearCoverCheck_sound
import Theorems.Thm_RealPinwheel_FiveSixths_checked_linear_D5_0004
import Theorems.Thm_RealPinwheel_FiveSixths_words_valid_D5_000
open RealPinwheel.FiveSixths

theorem solution (A : Instance 5) (hD : density A ≤ (5 : ℝ) / 6) :
    ∃ (L : ℕ) (S : ℕ → Fin 5), 0 < L ∧ L ≤ 32 ∧
      (∀ t, S (t + L) = S t) ∧ Valid A.period S := by
  let d : Fin 5 → ℝ := fun i => 1 / A.period i
  have ha : ∀ i, 0 < A.period i := fun i => lt_of_lt_of_le (by norm_num) (A.one_le i)
  have hpos : ∀ i, 0 < d i := fun i => one_div_pos.mpr (ha i)
  have hord : Antitone d := by
    intro i j hij
    exact one_div_le_one_div_of_le (ha i) (A.ordered hij)
  have hsum : (∑ i, if i.val < 5 then d i else 0) ≤ (5 : ℝ) / 6 := by
    simpa [density, d, Fin.sum_univ_succ, add_assoc] using hD
  obtain ⟨j, hb⟩ := linearCoverCheck_sound 5 216 codeFunctionD5 linearTreeD5_0004 RealPinwheel.FiveSixths.checked_linear_D5_0004 d hpos hord hsum
  exact RealPinwheel.FiveSixths.words_valid_D5_000 A j (by omega) (by omega) hb
