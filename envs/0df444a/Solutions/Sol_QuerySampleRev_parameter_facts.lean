-- Prove2me | solution 1 for QuerySampleRev.parameter_facts
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T05:25:57.088229+00:00
-- url     : https://prove2.me/submissions/54c0bba3-8bec-48a8-8485-6141e74fdb9a

import Mathlib
import Definitions.Def_QuerySampleRev_priceInterval

open QuerySampleRev in
theorem solution {c ε : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hε0 : 0 < ε) (hε : ε ≤ 1 / 128) :
    rho ε c * halfWidth ε c = 2 * ε ∧
    ε ^ (-c) / 2 ^ 7 ≤ (numHard ε c : ℝ) ∧ (numHard ε c : ℝ) ≤ 2 * ε ^ (-c) ∧
    rho ε c ≤ max (32 * ε) (ε ^ (1 - c) / 4) ∧ max (32 * ε) (ε ^ (1 - c) / 4) ≤ 1 / 4 ∧
    (∀ i ∈ Finset.Icc 1 (numHard ε c), ∀ j ∈ Finset.Icc 1 (numHard ε c), i ≠ j →
      Disjoint (priceInterval ε c i) (priceInterval ε c j)) ∧
    (∀ i ∈ Finset.Icc 1 (numHard ε c), priceInterval ε c i ⊆ Set.Icc (5 / 4) (3 / 2)) := by
  have hE1 : 1 ≤ ε ^ (-c) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hε0 (by linarith) (by linarith)
  obtain ⟨E, hEd⟩ : ∃ E, E = ε ^ (-c) := ⟨_, rfl⟩
  rw [← hEd] at hE1 ⊢
  have hEe : ε ^ (1 - c) = ε * E := by
    rw [hEd, sub_eq_add_neg, Real.rpow_add hε0, Real.rpow_one]
  rw [hEe]
  have hF0 : 0 ≤ E / 64 := by linarith
  have hFle : (⌊E / 64⌋₊ : ℝ) ≤ E / 64 := Nat.floor_le hF0
  have hFgt : E / 64 < (⌊E / 64⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hn : (numHard ε c : ℝ) = max 2 (⌊E / 64⌋₊ : ℝ) := by
    unfold numHard
    rw [← hEd, Nat.cast_max]
    norm_num
  have hn2 : (2 : ℝ) ≤ numHard ε c := by rw [hn]; exact le_max_left _ _
  have hnpos : (0 : ℝ) < numHard ε c := by linarith
  have h8 : (8 * (numHard ε c : ℝ)) ≠ 0 := (mul_pos (by norm_num) hnpos).ne'
  have hwn : halfWidth ε c * (numHard ε c : ℝ) = 1 / 8 := by
    unfold halfWidth
    rw [div_mul_eq_mul_div, one_mul, div_eq_div_iff h8 (by norm_num)]
    ring
  have hw0 : 0 < halfWidth ε c := by
    unfold halfWidth; exact div_pos one_pos (mul_pos (by norm_num) hnpos)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold rho
    have : 16 * (numHard ε c : ℝ) * ε * halfWidth ε c = 16 * ε * (halfWidth ε c * numHard ε c) := by
      ring
    rw [this, hwn]; ring
  · rw [hn]
    rcases le_or_gt E 256 with h | h
    · exact le_trans (by linarith) (le_max_left _ _)
    · exact le_trans (by linarith) (le_max_right _ _)
  · rw [hn]
    exact max_le (by linarith) (by linarith)
  · unfold rho
    rw [hn]
    rcases max_cases (2 : ℝ) (⌊E / 64⌋₊ : ℝ) with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]; exact le_trans (by linarith) (le_max_left _ _)
    · rw [h]
      refine le_trans ?_ (le_max_right _ _)
      nlinarith [mul_le_mul_of_nonneg_left hFle hε0.le]
  · refine max_le (by linarith) ?_
    have : ε * E ≤ 1 := by
      rw [← hEe]; exact Real.rpow_le_one hε0.le (by linarith) (by linarith)
    linarith
  · intro i hi j hj hij
    unfold priceInterval bPt aPt
    rw [Set.Ioc_disjoint_Ioc]
    rcases lt_or_gt_of_ne hij with h | h
    · have hij' : (i : ℝ) + 1 ≤ j := by exact_mod_cast h
      have key : 3 / 2 - 2 * (j : ℝ) * halfWidth ε c + 2 * halfWidth ε c ≤
          3 / 2 - 2 * (i : ℝ) * halfWidth ε c := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hij') hw0.le]
      exact (min_le_right _ _).trans (key.trans (le_max_left _ _))
    · have hij' : (j : ℝ) + 1 ≤ i := by exact_mod_cast h
      have key : 3 / 2 - 2 * (i : ℝ) * halfWidth ε c + 2 * halfWidth ε c ≤
          3 / 2 - 2 * (j : ℝ) * halfWidth ε c := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hij') hw0.le]
      exact (min_le_left _ _).trans (key.trans (le_max_right _ _))
  · intro i hi x hx
    rw [Finset.mem_Icc] at hi
    have h1 : (1 : ℝ) ≤ i := by exact_mod_cast hi.1
    have h2 : (i : ℝ) ≤ numHard ε c := by exact_mod_cast hi.2
    unfold priceInterval bPt aPt at hx
    obtain ⟨hx1, hx2⟩ := hx
    have e1 : (i : ℝ) * halfWidth ε c ≤ numHard ε c * halfWidth ε c :=
      mul_le_mul_of_nonneg_right h2 hw0.le
    have e2 : halfWidth ε c ≤ (i : ℝ) * halfWidth ε c := by
      have := mul_le_mul_of_nonneg_right h1 hw0.le
      linarith
    constructor
    · linarith
    · linarith
