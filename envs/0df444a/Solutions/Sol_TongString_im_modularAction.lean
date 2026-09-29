-- Prove2me | solution 1 for TongString.im_modularAction
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T14:53:28.689921+00:00
-- url     : https://prove2.me/submissions/42173baf-4080-4bff-b2e5-b3716d657728

import Mathlib
import Definitions.Def_TongString_modular_action

open TongString in
theorem solution (a b c d : ℤ) (h : a * d - b * c = 1) (τ : ℂ) (hτ : 0 < τ.im) :
    (modularAction a b c d τ).im = τ.im / Complex.normSq (c * τ + d) := by
  have key : (modularAction a b c d τ).im =
      (((a : ℂ) * τ + b).im * ((c : ℂ) * τ + d).re - ((a : ℂ) * τ + b).re * ((c : ℂ) * τ + d).im)
        / Complex.normSq ((c : ℂ) * τ + d) := by
    unfold modularAction
    rw [Complex.div_im, sub_div]
  rw [key]
  congr 1
  have h' : ((a : ℝ) * d - b * c) = 1 := by exact_mod_cast h
  simp only [Complex.add_im, Complex.mul_im, Complex.add_re, Complex.mul_re,
    Complex.intCast_re, Complex.intCast_im]
  linear_combination τ.im * h'
