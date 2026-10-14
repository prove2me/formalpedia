-- Prove2me | solution 1 for ThreeSumSharpTail.full_d_call_total
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-13T19:14:38.083584+00:00
-- url     : https://prove2.me/submissions/a6c3eb9a-5e6b-437d-b5f7-656e3d01b4a8

import Mathlib
import Theorems.Thm_ThreeSumSharpTail_full_d_call_balance

set_option autoImplicit false
set_option relaxedAutoImplicit false

theorem solution (n D g s C C' t w : ℝ)
    (hD : 1 ≤ D) (hn : 1 ≤ n) (hs : 0 ≤ s) (hsHalf : s ≤ 1 / 2)
    (hgLo : D ^ (s / 2) ≤ g) (hgHi : g ≤ 2 * D ^ (s / 2))
    (hbuild : D ^ (1 + s) ≤ n) (hC : 0 ≤ C) (hC' : 0 ≤ C')
    (_hw0 : 0 ≤ w) (hw : w ≤ n ^ 2 / Real.sqrt D)
    (ht : t ≤ C *
      (n ^ 2 * (Real.log D + 1) ^ 2 / D ^ s +
        w * D ^ (1 / 2 - s) * (Real.log D + 1) + n * D + w + 1)) :
    4 * n * g * (t + C' * n ^ 2 / Real.sqrt D) ≤
      (64 * C + 8 * C') *
        (n ^ 3 * D ^ (-s / 2) * (Real.log D + 1) ^ 2) := by
  have hbal := ThreeSumSharpTail.full_d_call_balance D n g s hD hn hs hsHalf
    hgLo hgHi hbuild
  rcases hbal with ⟨hAexp, hBexp, hCexp, hDexp, hGinv⟩
  have hDpos : 0 < D := lt_of_lt_of_le (by norm_num) hD
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hgpos : 0 < g := lt_of_lt_of_le (Real.rpow_pos_of_pos hDpos _) hgLo
  have hL : 1 ≤ Real.log D + 1 := by
    have := Real.log_nonneg hD
    linarith
  have hLsq : 1 ≤ (Real.log D + 1) ^ 2 := by nlinarith [hL]
  have hLnonneg : 0 ≤ Real.log D + 1 := le_trans (by norm_num) hL
  have hLleSq : Real.log D + 1 ≤ (Real.log D + 1) ^ 2 := by
    simpa [pow_two] using mul_le_mul_of_nonneg_right hL hLnonneg
  let P : ℝ := D ^ (-s / 2)
  let L : ℝ := Real.log D + 1
  let S : ℝ := n ^ 2 * L ^ 2 / D ^ s +
    w * D ^ (1 / 2 - s) * L + n * D + w + 1
  let X : ℝ := n ^ 3 * P * L ^ 2
  have hLsq' : 1 ≤ L ^ 2 := by simpa [L] using hLsq
  have hLleSq' : L ≤ L ^ 2 := by simpa [L] using hLleSq
  have hPnonneg : 0 ≤ P := by dsimp [P]; positivity
  have hLnonneg : 0 ≤ L := le_trans (by norm_num) hL
  have hXnonneg : 0 ≤ X := by dsimp [X, P, L]; positivity
  have hDs_le_n : D ^ s ≤ n := by
    exact (Real.rpow_le_rpow_of_exponent_le hD (by linarith)).trans hbuild
  have hn_le_nsq : n ≤ n ^ 2 := by
    calc n = 1 * n := by ring
      _ ≤ n * n := mul_le_mul_of_nonneg_right hn (by linarith)
      _ = n ^ 2 := by ring
  have hDs_le_nsq : D ^ s ≤ n ^ 2 := hDs_le_n.trans hn_le_nsq
  have hDs_le_nsqLsq : D ^ s ≤ n ^ 2 * L ^ 2 := by
    calc D ^ s ≤ n ^ 2 := hDs_le_nsq
      _ = n ^ 2 * 1 := by ring
      _ ≤ n ^ 2 * L ^ 2 := mul_le_mul_of_nonneg_left hLsq' (sq_nonneg n)
  have htermA : n * g * (n ^ 2 * L ^ 2 / D ^ s) ≤ 2 * X := by
    have hbal : g / D ^ s ≤ 2 * P := by simpa [P] using hAexp
    have hfac : 0 ≤ n ^ 3 * L ^ 2 := by positivity
    calc
      n * g * (n ^ 2 * L ^ 2 / D ^ s) = n ^ 3 * L ^ 2 * (g / D ^ s) := by
        dsimp [L]
        ring
      _ ≤ n ^ 3 * L ^ 2 * (2 * P) := mul_le_mul_of_nonneg_left hbal hfac
      _ = 2 * X := by dsimp [X]; ring
  have htermB : n * g * (w * D ^ (1 / 2 - s) * L) ≤ 2 * X := by
    have hscaled := mul_le_mul_of_nonneg_right hw (by positivity :
      0 ≤ n * g * D ^ (1 / 2 - s) * L)
    have hbal : g * D ^ (1 / 2 - s) / Real.sqrt D ≤ 2 * P := by
      simpa [P] using hBexp
    calc
      n * g * (w * D ^ (1 / 2 - s) * L) =
          w * (n * g * D ^ (1 / 2 - s) * L) := by ring
      _ ≤ (n ^ 2 / Real.sqrt D) * (n * g * D ^ (1 / 2 - s) * L) := hscaled
      _ = n ^ 3 * L * (g * D ^ (1 / 2 - s) / Real.sqrt D) := by ring
      _ ≤ n ^ 3 * L * (2 * P) :=
        mul_le_mul_of_nonneg_left hbal (by positivity)
      _ ≤ 2 * X := by
        dsimp [X]
        calc
          n ^ 3 * L * (2 * P) = 2 * n ^ 3 * P * L := by ring
          _ ≤ 2 * n ^ 3 * P * L ^ 2 :=
            mul_le_mul_of_nonneg_left hLleSq' (by positivity)
          _ = 2 * (n ^ 3 * P * L ^ 2) := by ring
  have htermC : n * g * (n * D) ≤ 2 * X := by
    have hbal : g * D ≤ 2 * n * P := by simpa [P] using hDexp
    calc
      n * g * (n * D) = n ^ 2 * (g * D) := by ring
      _ ≤ n ^ 2 * (2 * n * P) :=
        mul_le_mul_of_nonneg_left hbal (sq_nonneg n)
      _ ≤ 2 * X := by
        dsimp [X]
        calc
          n ^ 2 * (2 * n * P) = 2 * n ^ 3 * P := by ring
          _ = (2 * n ^ 3 * P) * 1 := by ring
          _ ≤ (2 * n ^ 3 * P) * L ^ 2 :=
            mul_le_mul_of_nonneg_left hLsq' (by positivity)
          _ = 2 * (n ^ 3 * P * L ^ 2) := by ring
  have htermD : n * g * w ≤ 2 * X := by
    have hscaled := mul_le_mul_of_nonneg_right hw (by positivity : 0 ≤ n * g)
    have hbal : g / Real.sqrt D ≤ 2 * P := by simpa [P] using hCexp
    calc
      n * g * w = w * (n * g) := by ring
      _ ≤ (n ^ 2 / Real.sqrt D) * (n * g) := hscaled
      _ = n ^ 3 * (g / Real.sqrt D) := by ring
      _ ≤ n ^ 3 * (2 * P) := mul_le_mul_of_nonneg_left hbal (by positivity)
      _ ≤ 2 * X := by
        dsimp [X]
        calc
          n ^ 3 * (2 * P) = 2 * n ^ 3 * P := by ring
          _ = (2 * n ^ 3 * P) * 1 := by ring
          _ ≤ (2 * n ^ 3 * P) * L ^ 2 :=
            mul_le_mul_of_nonneg_left hLsq' (by positivity)
          _ = 2 * (n ^ 3 * P * L ^ 2) := by ring
  have htermE : n * g ≤ 2 * X := by
    have hbal : g / D ^ s ≤ 2 * P := by simpa [P] using hAexp
    have hgScaled : g ≤ (2 * P) * D ^ s := (div_le_iff₀
      (Real.rpow_pos_of_pos hDpos s)).mp hbal
    calc
      n * g ≤ n * ((2 * P) * D ^ s) := mul_le_mul_of_nonneg_left hgScaled (le_of_lt hnpos)
      _ ≤ 2 * n ^ 3 * P * L ^ 2 := by
        calc
          n * ((2 * P) * D ^ s) = 2 * n * P * D ^ s := by ring
          _ ≤ 2 * n * P * (n ^ 2 * L ^ 2) :=
            mul_le_mul_of_nonneg_left hDs_le_nsqLsq (by positivity)
          _ = 2 * n ^ 3 * P * L ^ 2 := by ring
      _ = 2 * X := by dsimp [X]; ring
  have hsum : n * g * S ≤ 10 * X := by
    calc
      n * g * S = n * g * (n ^ 2 * L ^ 2 / D ^ s) +
          n * g * (w * D ^ (1 / 2 - s) * L) + n * g * (n * D) +
          n * g * w + n * g := by dsimp [S]; ring
      _ ≤ 2 * X + 2 * X + 2 * X + 2 * X + 2 * X := by
        exact add_le_add (add_le_add (add_le_add (add_le_add htermA htermB) htermC) htermD) htermE
      _ = 10 * X := by ring
  have hmain : 4 * n * g * t ≤ 40 * C * X := by
    have ht' := mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ 4 * n * g)
    calc
      4 * n * g * t ≤ 4 * n * g * (C * S) := by simpa [S] using ht'
      _ = 4 * C * (n * g * S) := by ring
      _ ≤ 4 * C * (10 * X) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = 40 * C * X := by ring
  have hextra : 4 * n * g * (C' * n ^ 2 / Real.sqrt D) ≤ 8 * C' * X := by
    have hbal : g / Real.sqrt D ≤ 2 * P := by simpa [P] using hCexp
    calc
      4 * n * g * (C' * n ^ 2 / Real.sqrt D) =
          4 * C' * n ^ 3 * (g / Real.sqrt D) := by ring
      _ ≤ 4 * C' * n ^ 3 * (2 * P) :=
        mul_le_mul_of_nonneg_left hbal (by positivity)
      _ ≤ 8 * C' * X := by
        dsimp [X]
        calc
          4 * C' * n ^ 3 * (2 * P) = 8 * C' * n ^ 3 * P := by ring
          _ = (8 * C' * n ^ 3 * P) * 1 := by ring
          _ ≤ (8 * C' * n ^ 3 * P) * L ^ 2 :=
            mul_le_mul_of_nonneg_left hLsq' (by positivity)
          _ = 8 * C' * (n ^ 3 * P * L ^ 2) := by ring
  have hcoeff : 40 * C * X + 8 * C' * X ≤ (64 * C + 8 * C') * X := by
    have hCX : 0 ≤ 24 * C * X := by positivity
    nlinarith
  calc
    4 * n * g * (t + C' * n ^ 2 / Real.sqrt D) =
        4 * n * g * t + 4 * n * g * (C' * n ^ 2 / Real.sqrt D) := by ring
    _ ≤ 40 * C * X + 8 * C' * X := add_le_add hmain hextra
    _ ≤ (64 * C + 8 * C') * X := hcoeff
    _ = (64 * C + 8 * C') *
        (n ^ 3 * D ^ (-s / 2) * (Real.log D + 1) ^ 2) := by dsimp [X, P, L]

#print axioms solution
