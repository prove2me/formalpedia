-- Prove2me | solution 1 for RealPinwheel.FiveSixths.density_certificate_3
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T03:23:41.329655+00:00
-- url     : https://prove2.me/submissions/f318bdce-ffe7-4cdb-852d-70d2f46cdd1f

import Theorems.Thm_RealPinwheel_FiveSixths_codeCheck_sound
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD3
open RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private theorem coverage (d : Fin 3 → ℝ) (hpos : ∀ i, 0 < d i) (hord : Antitone d)
    (hsum : ∑ i, d i ≤ (5 : ℝ) / 6) :
    ∃ k : Fin certificateD3.size, codeBox certificateD3[k.val] d := by
  have p0 := hpos 0
  have p1 := hpos 1
  have p2 := hpos 2
  have o0 : d 1 ≤ d 0 := hord (by decide)
  have o1 : d 2 ≤ d 1 := hord (by decide)
  have hs : d 0 + d 1 + d 2 ≤ (5 : ℝ) / 6 := by
    simpa [Fin.sum_univ_succ, add_assoc] using hsum
  have hc : ((d 0 ≤ (5 : ℝ) / 6) ∧ (d 1 ≤ (1 : ℝ) / 12) ∧ (d 2 ≤ (1 : ℝ) / 12)) ∨
    ((d 0 ≤ (7 : ℝ) / 10) ∧ (d 1 < (1 : ℝ) / 5) ∧ (d 2 ≤ (1 : ℝ) / 10)) ∨
    ((d 0 < (3 : ℝ) / 5) ∧ (d 1 ≤ (3 : ℝ) / 10) ∧ (d 2 ≤ (1 : ℝ) / 10)) ∨
    ((d 0 < (1 : ℝ) / 2) ∧ (d 1 ≤ (2 : ℝ) / 5) ∧ (d 2 ≤ (1 : ℝ) / 10)) ∨
    ((d 0 < (2 : ℝ) / 3) ∧ (d 1 ≤ (2 : ℝ) / 9) ∧ (d 2 ≤ (1 : ℝ) / 9)) ∨
    ((d 0 ≤ (5 : ℝ) / 9) ∧ (d 1 < (1 : ℝ) / 3) ∧ (d 2 ≤ (1 : ℝ) / 9)) ∨
    ((d 0 ≤ (4 : ℝ) / 9) ∧ (d 1 ≤ (4 : ℝ) / 9) ∧ (d 2 ≤ (1 : ℝ) / 9)) ∨
    ((d 0 ≤ (3 : ℝ) / 4) ∧ (d 1 ≤ (1 : ℝ) / 8) ∧ (d 2 ≤ (1 : ℝ) / 8)) ∨
    ((d 0 ≤ (5 : ℝ) / 8) ∧ (d 1 < (1 : ℝ) / 4) ∧ (d 2 ≤ (1 : ℝ) / 8)) ∨
    ((d 0 ≤ (3 : ℝ) / 8) ∧ (d 1 ≤ (3 : ℝ) / 8) ∧ (d 2 ≤ (1 : ℝ) / 4)) ∨
    ((d 0 ≤ (5 : ℝ) / 7) ∧ (d 1 ≤ (1 : ℝ) / 7) ∧ (d 2 ≤ (1 : ℝ) / 7)) ∨
    ((d 0 ≤ (4 : ℝ) / 7) ∧ (d 1 ≤ (2 : ℝ) / 7) ∧ (d 2 ≤ (1 : ℝ) / 7)) ∨
    ((d 0 ≤ (3 : ℝ) / 7) ∧ (d 1 ≤ (2 : ℝ) / 7) ∧ (d 2 ≤ (2 : ℝ) / 7)) ∨
    ((d 0 < (1 : ℝ) / 2) ∧ (d 1 ≤ (1 : ℝ) / 3) ∧ (d 2 ≤ (1 : ℝ) / 6)) ∨
    ((d 0 ≤ (3 : ℝ) / 5) ∧ (d 1 ≤ (1 : ℝ) / 5) ∧ (d 2 ≤ (1 : ℝ) / 5)) ∨
    ((d 0 ≤ (2 : ℝ) / 5) ∧ (d 1 ≤ (2 : ℝ) / 5) ∧ (d 2 ≤ (1 : ℝ) / 5)) ∨
    ((d 0 ≤ (1 : ℝ) / 2) ∧ (d 1 ≤ (1 : ℝ) / 4) ∧ (d 2 ≤ (1 : ℝ) / 4)) ∨
    ((d 0 ≤ (1 : ℝ) / 3) ∧ (d 1 ≤ (1 : ℝ) / 3) ∧ (d 2 ≤ (1 : ℝ) / 3)) := by
    grind (splits := 10000)
  rcases hc with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · refine ⟨⟨0, by decide⟩, ?_⟩
    intro i
    fin_cases i <;> norm_num [codeBox, codeNum, codeDen, codeStrict, certificateD3] <;> tauto
  · refine ⟨⟨1, by decide⟩, ?_⟩
    intro i
    fin_cases i <;> norm_num [codeBox, codeNum, codeDen, codeStrict, certificateD3] <;> tauto
  · refine ⟨⟨2, by decide⟩, ?_⟩
    intro i
    fin_cases i <;> norm_num [codeBox, codeNum, codeDen, codeStrict, certificateD3] <;> tauto
  · refine ⟨⟨3, by decide⟩, ?_⟩
    intro i
    fin_cases i <;> norm_num [codeBox, codeNum, codeDen, codeStrict, certificateD3] <;> tauto
  · refine ⟨⟨4, by decide⟩, ?_⟩
    intro i
    fin_cases i <;> norm_num [codeBox, codeNum, codeDen, codeStrict, certificateD3] <;> tauto
  · refine ⟨⟨5, by decide⟩, ?_⟩
    intro i
    fin_cases i <;> norm_num [codeBox, codeNum, codeDen, codeStrict, certificateD3] <;> tauto
  · refine ⟨⟨6, by decide⟩, ?_⟩
    intro i
    fin_cases i <;> norm_num [codeBox, codeNum, codeDen, codeStrict, certificateD3] <;> tauto
  · refine ⟨⟨7, by decide⟩, ?_⟩
    intro i
    fin_cases i <;> norm_num [codeBox, codeNum, codeDen, codeStrict, certificateD3] <;> tauto
  · refine ⟨⟨8, by decide⟩, ?_⟩
    intro i
    fin_cases i <;> norm_num [codeBox, codeNum, codeDen, codeStrict, certificateD3] <;> tauto
  · refine ⟨⟨9, by decide⟩, ?_⟩
    intro i
    fin_cases i <;> norm_num [codeBox, codeNum, codeDen, codeStrict, certificateD3] <;> tauto
  · refine ⟨⟨10, by decide⟩, ?_⟩
    intro i
    fin_cases i <;> norm_num [codeBox, codeNum, codeDen, codeStrict, certificateD3] <;> tauto
  · refine ⟨⟨11, by decide⟩, ?_⟩
    intro i
    fin_cases i <;> norm_num [codeBox, codeNum, codeDen, codeStrict, certificateD3] <;> tauto
  · refine ⟨⟨12, by decide⟩, ?_⟩
    intro i
    fin_cases i <;> norm_num [codeBox, codeNum, codeDen, codeStrict, certificateD3] <;> tauto
  · refine ⟨⟨13, by decide⟩, ?_⟩
    intro i
    fin_cases i <;> norm_num [codeBox, codeNum, codeDen, codeStrict, certificateD3] <;> tauto
  · refine ⟨⟨14, by decide⟩, ?_⟩
    intro i
    fin_cases i <;> norm_num [codeBox, codeNum, codeDen, codeStrict, certificateD3] <;> tauto
  · refine ⟨⟨15, by decide⟩, ?_⟩
    intro i
    fin_cases i <;> norm_num [codeBox, codeNum, codeDen, codeStrict, certificateD3] <;> tauto
  · refine ⟨⟨16, by decide⟩, ?_⟩
    intro i
    fin_cases i <;> norm_num [codeBox, codeNum, codeDen, codeStrict, certificateD3] <;> tauto
  · refine ⟨⟨17, by decide⟩, ?_⟩
    intro i
    fin_cases i <;> norm_num [codeBox, codeNum, codeDen, codeStrict, certificateD3] <;> tauto

theorem solution (A : Instance 3) (hD : density A ≤ (5 : ℝ) / 6) :
    ∃ (L : ℕ) (S : ℕ → Fin 3), 0 < L ∧ L ≤ 12 ∧
      (∀ t, S (t + L) = S t) ∧ Valid A.period S := by
  have hcheck : (certificateD3.all fun c => codeCheck 3 (by decide) c &&
      decide ((codeWord 3 (by decide) c).size ≤ 12)) = true := by decide +kernel
  let d : Fin 3 → ℝ := fun i => 1 / A.period i
  have ha : ∀ i, 0 < A.period i := fun i => lt_of_lt_of_le (by norm_num) (A.one_le i)
  have hpos : ∀ i, 0 < d i := fun i => one_div_pos.mpr (ha i)
  have hord : Antitone d := by
    intro i j hij
    exact one_div_le_one_div_of_le (ha i) (A.ordered hij)
  obtain ⟨k, hk⟩ := coverage d hpos hord hD
  have hc := Array.all_eq_true.mp hcheck k.val k.isLt
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨L, S, hL, hp, hv⟩ := codeCheck_sound (by decide : 0 < 3) certificateD3[k.val] hc.1 A.period ha hk
  exact ⟨L, S, hp.1, hL.trans_le hc.2, hp.2, hv⟩
