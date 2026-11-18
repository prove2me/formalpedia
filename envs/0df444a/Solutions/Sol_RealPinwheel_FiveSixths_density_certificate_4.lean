-- Prove2me | solution 1 for RealPinwheel.FiveSixths.density_certificate_4
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:18:02.196677+00:00
-- url     : https://prove2.me/submissions/6948138b-bf66-4d81-905c-f12844078016

import Theorems.Thm_RealPinwheel_FiveSixths_coverage_D4
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D4
import Theorems.Thm_RealPinwheel_FiveSixths_codeCheck_sound
open RealPinwheel.FiveSixths
theorem solution (A : Instance 4) (hD : density A ≤ (5 : ℝ) / 6) :
    ∃ (L : ℕ) (S : ℕ → Fin 4), 0 < L ∧ L ≤ 18 ∧
      (∀ t, S (t + L) = S t) ∧ Valid A.period S := by
  have hcheck := checked_D4
  let d : Fin 4 → ℝ := fun i => 1 / A.period i
  have ha : ∀ i, 0 < A.period i := fun i => lt_of_lt_of_le (by norm_num) (A.one_le i)
  have hpos : ∀ i, 0 < d i := fun i => one_div_pos.mpr (ha i)
  have hord : Antitone d := by
    intro i j hij
    exact one_div_le_one_div_of_le (ha i) (A.ordered hij)
  obtain ⟨k, hk⟩ := coverage_D4 d hpos hord hD
  have hc := Array.all_eq_true.mp hcheck k.val k.isLt
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨L, S, hL, hp, hv⟩ := codeCheck_sound (by decide : 0 < 4) certificateD4[k.val] hc.1 A.period ha hk
  exact ⟨L, S, hp.1, hL.trans_le hc.2, hp.2, hv⟩
