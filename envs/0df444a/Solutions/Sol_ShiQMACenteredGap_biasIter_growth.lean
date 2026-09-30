-- Prove2me | solution 1 for ShiQMACenteredGap.biasIter_growth
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-30T07:03:52.849842+00:00
-- url     : https://prove2.me/submissions/b2aee495-ef12-42c7-af23-b94493f69d7d

import Definitions.Def_ShiQMACenteredGap

set_option autoImplicit false
open ShiQMAErrorIteration ShiQMACenteredGap

private theorem biasStep_mono {d e : ℝ} (hd : 0 ≤ d) (hde : d ≤ e)
    (he : e ≤ 1 / 2) : biasStep d ≤ biasStep e := by
  have hed : e * d ≤ 1 / 4 := by nlinarith [sq_nonneg (e - d)]
  have hsq : e ^ 2 + e * d + d ^ 2 ≤ 3 / 4 := by
    nlinarith [mul_nonneg (show 0 ≤ e by linarith) (show 0 ≤ 1 / 2 - e by linarith),
      mul_nonneg hd (show 0 ≤ 1 / 2 - d by linarith)]
  have h := mul_nonneg (show 0 ≤ e - d by linarith)
    (show 0 ≤ 3 / 2 - 2 * (e ^ 2 + e * d + d ^ 2) by linarith)
  dsimp [biasStep]
  nlinarith

private theorem biasStep_bounds {d : ℝ} (hd : 0 ≤ d) (hd' : d ≤ 1 / 2) :
    0 ≤ biasStep d ∧ biasStep d ≤ 1 / 2 := by
  constructor
  · have h := biasStep_mono (d := 0) (e := d) (by norm_num) hd hd'
    norm_num [biasStep] at h ⊢
    exact h
  · have h := biasStep_mono hd hd' (le_refl (1 / 2))
    norm_num [biasStep] at h ⊢
    exact h

/-- Until a constant bias is reached, every majority round grows the bias geometrically. -/
private theorem biasStep_growth {d : ℝ} (hd : 0 ≤ d) (hd' : d ≤ 1 / 6) :
    (4 / 3 : ℝ) * d ≤ biasStep d := by
  have hs : d ^ 2 ≤ 1 / 36 := by nlinarith
  have h := mul_nonneg hd (show 0 ≤ 1 / 6 - 2 * d ^ 2 by linarith)
  dsimp [biasStep]
  nlinarith

private theorem biasStep_capped_growth {d : ℝ} (hd : 0 ≤ d) (hd' : d ≤ 1 / 2) :
    min (1 / 6) ((4 / 3 : ℝ) * d) ≤ biasStep d := by
  by_cases h : d ≤ 1 / 6
  · exact (min_le_right _ _).trans (biasStep_growth hd h)
  · have hmono := biasStep_mono (d := 1 / 6) (e := d) (by norm_num) (by linarith) hd'
    have hconst : (1 / 6 : ℝ) ≤ biasStep (1 / 6) := by norm_num [biasStep]
    exact (min_le_left _ _).trans (hconst.trans hmono)

private theorem biasIter_bounds {d : ℝ} (hd : 0 ≤ d) (hd' : d ≤ 1 / 2) (r : Nat) :
    0 ≤ biasIter d r ∧ biasIter d r ≤ 1 / 2 := by
  induction r with
  | zero => exact ⟨hd, hd'⟩
  | succ r ih => exact biasStep_bounds ih.1 ih.2

theorem solution {d : ℝ} (hd : 0 ≤ d) (hd' : d ≤ 1 / 2) (r : Nat) :
    min (1 / 6) (((4 : ℝ) / 3) ^ r * d) ≤ biasIter d r := by
  induction r with
  | zero => simpa [biasIter] using min_le_right (1 / 6 : ℝ) d
  | succ r ih =>
    have hb := biasIter_bounds hd hd' r
    have hg := biasStep_capped_growth hb.1 hb.2
    change min (1 / 6) (((4 : ℝ) / 3) ^ (r + 1) * d) ≤ biasStep (biasIter d r)
    rw [pow_succ]
    by_cases h : (1 / 6 : ℝ) ≤ ((4 : ℝ) / 3) ^ r * d
    · rw [min_eq_left h] at ih
      have hcap : (1 / 6 : ℝ) ≤ (4 / 3) * biasIter d r := by linarith
      rw [min_eq_left hcap] at hg
      exact (min_le_left _ _).trans hg
    · rw [min_eq_right (le_of_not_ge h)] at ih
      apply le_trans _ hg
      apply min_le_min_left
      nlinarith
