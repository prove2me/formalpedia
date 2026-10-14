-- Prove2me | solution 1 for ThreeSumSharpTail.full_d_extra_total
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-13T19:14:42.398087+00:00
-- url     : https://prove2.me/submissions/ec958595-b630-4f22-9c93-4929400c9b32

import Definitions.Def_APSPSource_ThreeSumApsp_Sec3_Parameters
import Theorems.Thm_ThreeSumSharpTail_full_d_call_balance
import Mathlib

open ThreeSumApsp

/-- The scan, prime selection and instance construction terms of the actual full-D host. -/
theorem solution (n D g : ℕ) (a s κ C : ℝ)
    (hn : 3 ≤ n) (hD : 1 ≤ D) (hDa : (D : ℝ) ≤ (n : ℝ) ^ a)
    (hs0 : 0 ≤ s) (hsHalf : s ≤ 1 / 2)
    (hgLo : (D : ℝ) ^ (s / 2) ≤ g) (hgHi : (g : ℝ) ≤ 2 * (D : ℝ) ^ (s / 2))
    (hbuild : a * (1 + s) ≤ 1)
    (hprime : Real.logb 2 7 + 3 * a / 2 ≤ 3 - a * s / 2)
    (hκ : 1 ≤ κ) (hC : 0 ≤ C) :
    C * (termScans n g κ + termPrime strassen n D + termBuild n D g) ≤
      4 * C * (κ * ((n : ℝ) ^ 3 * (D : ℝ) ^ (-s / 2) * Real.log n ^ 2)) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn0 : (0 : ℝ) < n := zero_lt_one.trans_le hn1
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hD0 : (0 : ℝ) < D := zero_lt_one.trans_le hD1
  have hlog : 1 ≤ Real.log n := Real.one_le_log_natCast_of_three_le hn
  have hfit : (D : ℝ) ^ (1 + s) ≤ n := by
    calc
      (D : ℝ) ^ (1 + s) ≤ ((n : ℝ) ^ a) ^ (1 + s) :=
        Real.rpow_le_rpow hD0.le hDa (by linarith)
      _ = (n : ℝ) ^ (a * (1 + s)) := by rw [Real.rpow_mul hn0.le]
      _ ≤ (n : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hn1 hbuild
      _ = n := Real.rpow_one _
  obtain ⟨_, _, _, hgD, hscan⟩ := ThreeSumSharpTail.full_d_call_balance
    (D : ℝ) (n : ℝ) (g : ℝ) s hD1 hn1 hs0 hsHalf hgLo hgHi hfit
  set S := (n : ℝ) ^ 3 * (D : ℝ) ^ (-s / 2) with hS
  set X := κ * (S * Real.log n ^ 2) with hX
  have hS0 : 0 ≤ S := by positivity
  have hSX : S ≤ X := by
    rw [hX]
    calc
      S = 1 * (S * 1) := by ring
      _ ≤ κ * (S * Real.log n ^ 2) := by gcongr; exact one_le_pow₀ hlog
  have hκSLX : κ * (S * Real.log n) ≤ X := by
    rw [hX]
    gcongr
    exact le_self_pow₀ hlog two_ne_zero
  have hscan' : termScans n g κ ≤ X := by
    calc
      termScans n g κ = κ * ((n : ℝ) ^ 3 * Real.log n) * (1 / (g : ℝ)) := by
        unfold termScans
        ring
      _ ≤ κ * ((n : ℝ) ^ 3 * Real.log n) * (D : ℝ) ^ (-s / 2) := by
        gcongr
      _ = κ * (S * Real.log n) := by rw [hS]; ring
      _ ≤ X := hκSLX
  have hlow : (n : ℝ) ^ (3 - a * s / 2) ≤ S := by
    have hsave : (n : ℝ) ^ (-a * s / 2) ≤ (D : ℝ) ^ (-s / 2) := by
      calc
        (n : ℝ) ^ (-a * s / 2) = ((n : ℝ) ^ a) ^ (-s / 2) := by
          rw [← Real.rpow_mul hn0.le]
          congr 1
          ring
        _ ≤ (D : ℝ) ^ (-s / 2) := Real.rpow_le_rpow_of_nonpos hD0 hDa (by linarith)
    calc
      (n : ℝ) ^ (3 - a * s / 2) = (n : ℝ) ^ 3 * (n : ℝ) ^ (-a * s / 2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_add hn0]
        congr 1
        push_cast
        ring
      _ ≤ (n : ℝ) ^ 3 * (D : ℝ) ^ (-s / 2) := by gcongr
      _ = S := rfl
  have hprime' : termPrime strassen n D ≤ X := by
    calc
      termPrime strassen n D = (n : ℝ) ^ Real.logb 2 7 * (D : ℝ) ^ (3 / 2 : ℝ) := rfl
      _ ≤ (n : ℝ) ^ Real.logb 2 7 * ((n : ℝ) ^ a) ^ (3 / 2 : ℝ) := by gcongr
      _ = (n : ℝ) ^ (Real.logb 2 7 + 3 * a / 2) := by
        rw [← Real.rpow_mul hn0.le, ← Real.rpow_add hn0]
        congr 1
        ring
      _ ≤ (n : ℝ) ^ (3 - a * s / 2) := Real.rpow_le_rpow_of_exponent_le hn1 hprime
      _ ≤ S := hlow
      _ ≤ X := hSX
  have hbuild' : termBuild n D g ≤ 2 * X := by
    calc
      termBuild n D g = (n : ℝ) ^ 2 * ((g : ℝ) * D) := by unfold termBuild; ring
      _ ≤ (n : ℝ) ^ 2 * (2 * n * (D : ℝ) ^ (-s / 2)) := by gcongr
      _ = 2 * S := by rw [hS]; ring
      _ ≤ 2 * X := by gcongr
  calc
    C * (termScans n g κ + termPrime strassen n D + termBuild n D g) ≤ C * (4 * X) := by
      gcongr
      linarith
    _ = 4 * C * (κ * ((n : ℝ) ^ 3 * (D : ℝ) ^ (-s / 2) * Real.log n ^ 2)) := by
      rw [hX, hS]
      ring

#print axioms solution
