-- Prove2me | solution 1 for RealPinwheel.FiveSixths.density_certificate_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T03:23:39.970552+00:00
-- url     : https://prove2.me/submissions/d6d916f2-dd51-4122-8260-37c96315be29

import Theorems.Thm_RealPinwheel_FiveSixths_codeCheck_sound
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD1
open RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private theorem coverage (d : Fin 1 → ℝ) (hpos : ∀ i, 0 < d i) (hord : Antitone d)
    (hsum : ∑ i, d i ≤ (5 : ℝ) / 6) :
    ∃ k : Fin certificateD1.size, codeBox certificateD1[k.val] d := by
  have p0 := hpos 0
  have hs : d 0 ≤ (5 : ℝ) / 6 := by
    simpa [Fin.sum_univ_succ, add_assoc] using hsum
  have hc : ((d 0 ≤ (1 : ℝ) / 1)) := by
    grind (splits := 10000)
  rcases hc with h
  · refine ⟨⟨0, by decide⟩, ?_⟩
    intro i
    fin_cases i <;> norm_num [codeBox, codeNum, codeDen, codeStrict, certificateD1] <;> first | tauto | linarith

theorem solution (A : Instance 1) (hD : density A ≤ (5 : ℝ) / 6) :
    ∃ (L : ℕ) (S : ℕ → Fin 1), 0 < L ∧ L ≤ 1 ∧
      (∀ t, S (t + L) = S t) ∧ Valid A.period S := by
  have hcheck : (certificateD1.all fun c => codeCheck 1 (by decide) c &&
      decide ((codeWord 1 (by decide) c).size ≤ 1)) = true := by decide +kernel
  let d : Fin 1 → ℝ := fun i => 1 / A.period i
  have ha : ∀ i, 0 < A.period i := fun i => lt_of_lt_of_le (by norm_num) (A.one_le i)
  have hpos : ∀ i, 0 < d i := fun i => one_div_pos.mpr (ha i)
  have hord : Antitone d := by
    intro i j hij
    exact one_div_le_one_div_of_le (ha i) (A.ordered hij)
  obtain ⟨k, hk⟩ := coverage d hpos hord hD
  have hc := Array.all_eq_true.mp hcheck k.val k.isLt
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨L, S, hL, hp, hv⟩ := codeCheck_sound (by decide : 0 < 1) certificateD1[k.val] hc.1 A.period ha hk
  exact ⟨L, S, hp.1, hL ▸ hc.2, hp.2, hv⟩
