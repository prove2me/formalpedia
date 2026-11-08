-- Prove2me | solution 1 for WasteNotWant.stage2_rule_optimal
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T22:16:34.630269+00:00
-- url     : https://prove2.me/submissions/3781c270-fb7a-4abf-9b94-309a50ec046f

import Mathlib
import Definitions.Def_WasteNotWant_Model

open WasteNotWant in
theorem solution (P : Params) {δ x q : ℝ} (hδ : 0 < δ) (hq : 0 ≤ q) (hqx : q ≤ x)
    (y : ℝ) :
    stage2Rule P δ x q y ∈ Set.Icc 0 (x - q) ∧
      IsMaxOn (fun r : ℝ => P.pf * min (demand P y) (q + r) - (P.c + δ) * r)
        (Set.Icc 0 (x - q)) (stage2Rule P δ x q y) := by
  have hpf : 0 < P.pf := by linarith [P.c_nonneg, P.cm_pos, P.c_add_cm_lt_pf]
  have hcd : 0 < P.c + δ := by linarith [P.c_nonneg]
  unfold stage2Rule
  generalize demand P y = D
  split_ifs with hk
  · refine ⟨⟨le_min (le_max_right _ _) (by linarith), min_le_right _ _⟩, ?_⟩
    rw [isMaxOn_iff]
    intro r hr
    obtain ⟨hr0, hr1⟩ := hr
    rcases le_total (D - q) 0 with h1 | h1
    · rw [max_eq_right h1, min_eq_left (show (0 : ℝ) ≤ x - q by linarith), add_zero,
        min_eq_left (by linarith : D ≤ q + r), min_eq_left (by linarith : D ≤ q)]
      nlinarith [mul_nonneg hcd.le hr0]
    · rw [max_eq_left h1]
      rcases le_total (D - q) (x - q) with h2 | h2
      · rw [min_eq_left h2, show q + (D - q) = D by ring, min_self]
        rcases le_total D (q + r) with h3 | h3
        · rw [min_eq_left h3]
          nlinarith [mul_nonneg hcd.le (by linarith : (0 : ℝ) ≤ r - (D - q))]
        · rw [min_eq_right h3]
          nlinarith [mul_nonneg hk.le (by linarith : (0 : ℝ) ≤ D - q - r)]
      · rw [min_eq_right h2, show q + (x - q) = x by ring, min_eq_right (by linarith : x ≤ D),
          min_eq_right (by linarith : q + r ≤ D)]
        nlinarith [mul_nonneg hk.le (by linarith : (0 : ℝ) ≤ x - q - r)]
  · refine ⟨⟨le_refl 0, by linarith⟩, ?_⟩
    rw [isMaxOn_iff]
    intro r hr
    obtain ⟨hr0, hr1⟩ := hr
    push_neg at hk
    rw [add_zero]
    rcases le_total D q with h1 | h1
    · rw [min_eq_left (by linarith : D ≤ q + r), min_eq_left h1]
      nlinarith [mul_nonneg hcd.le hr0]
    · rw [min_eq_right h1]
      have hm : min D (q + r) ≤ q + r := min_le_right _ _
      nlinarith [mul_le_mul_of_nonneg_left hm hpf.le, mul_nonneg (by linarith : (0 : ℝ) ≤ -(P.pf - (P.c + δ))) hr0]
