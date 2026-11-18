-- Prove2me | solution 1 for RealPinwheel.FiveSixths.density_certificate_2
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T03:23:40.80203+00:00
-- url     : https://prove2.me/submissions/45697a17-a5ec-42a0-91b8-409172252a7d

import Theorems.Thm_RealPinwheel_FiveSixths_codeCheck_sound
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD2
open RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private theorem coverage (d : Fin 2 → ℝ) (hpos : ∀ i, 0 < d i) (hord : Antitone d)
    (hsum : ∑ i, d i ≤ (5 : ℝ) / 6) :
    ∃ k : Fin certificateD2.size, codeBox certificateD2[k.val] d := by
  have p0 := hpos 0
  have p1 := hpos 1
  have o0 : d 1 ≤ d 0 := hord (by decide)
  have hs : d 0 + d 1 ≤ (5 : ℝ) / 6 := by
    simpa [Fin.sum_univ_succ, add_assoc] using hsum
  have hc : ((d 0 ≤ (5 : ℝ) / 6) ∧ (d 1 ≤ (1 : ℝ) / 6)) ∨
    ((d 0 ≤ (2 : ℝ) / 3) ∧ (d 1 ≤ (1 : ℝ) / 3)) ∨
    ((d 0 ≤ (1 : ℝ) / 2) ∧ (d 1 ≤ (1 : ℝ) / 2)) := by
    grind (splits := 10000)
  rcases hc with h | h | h
  · refine ⟨⟨0, by decide⟩, ?_⟩
    intro i
    fin_cases i <;> norm_num [codeBox, codeNum, codeDen, codeStrict, certificateD2] <;> tauto
  · refine ⟨⟨1, by decide⟩, ?_⟩
    intro i
    fin_cases i <;> norm_num [codeBox, codeNum, codeDen, codeStrict, certificateD2] <;> tauto
  · refine ⟨⟨2, by decide⟩, ?_⟩
    intro i
    fin_cases i <;> norm_num [codeBox, codeNum, codeDen, codeStrict, certificateD2] <;> tauto

theorem solution (A : Instance 2) (hD : density A ≤ (5 : ℝ) / 6) :
    ∃ (L : ℕ) (S : ℕ → Fin 2), 0 < L ∧ L ≤ 6 ∧
      (∀ t, S (t + L) = S t) ∧ Valid A.period S := by
  have hcheck : (certificateD2.all fun c => codeCheck 2 (by decide) c &&
      decide ((codeWord 2 (by decide) c).size ≤ 6)) = true := by decide +kernel
  let d : Fin 2 → ℝ := fun i => 1 / A.period i
  have ha : ∀ i, 0 < A.period i := fun i => lt_of_lt_of_le (by norm_num) (A.one_le i)
  have hpos : ∀ i, 0 < d i := fun i => one_div_pos.mpr (ha i)
  have hord : Antitone d := by
    intro i j hij
    exact one_div_le_one_div_of_le (ha i) (A.ordered hij)
  obtain ⟨k, hk⟩ := coverage d hpos hord hD
  have hc := Array.all_eq_true.mp hcheck k.val k.isLt
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨L, S, hL, hp, hv⟩ := codeCheck_sound (by decide : 0 < 2) certificateD2[k.val] hc.1 A.period ha hk
  exact ⟨L, S, hp.1, hL ▸ hc.2, hp.2, hv⟩
