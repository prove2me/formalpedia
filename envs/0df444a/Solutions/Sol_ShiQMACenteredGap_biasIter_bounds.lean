-- Prove2me | solution 1 for ShiQMACenteredGap.biasIter_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-30T08:35:34.13362+00:00
-- url     : https://prove2.me/submissions/5cbabb08-ad3e-4787-9ef9-3b125389ee9a

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

theorem solution {d : ℝ} (hd : 0 ≤ d) (hd' : d ≤ 1 / 2) (r : Nat) :
    0 ≤ biasIter d r ∧ biasIter d r ≤ 1 / 2 := by
  induction r with
  | zero => exact ⟨hd, hd'⟩
  | succ r ih => exact biasStep_bounds ih.1 ih.2

