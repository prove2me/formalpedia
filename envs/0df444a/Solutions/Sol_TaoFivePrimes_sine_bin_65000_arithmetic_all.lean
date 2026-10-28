-- Prove2me | solution 1 for TaoFivePrimes.sine_bin_65000_arithmetic_all
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T22:05:11.778861+00:00
-- url     : https://prove2.me/submissions/757aafd6-2fd2-41a4-9e77-c152c1ac4fcf

import Definitions.Def_TaoFivePrimes_SineBinData65k
import Definitions.Def_TaoFivePrimes_SineBinArithmetic65k
import Mathlib.Tactic
import Theorems.Thm_TaoFivePrimes_sine_bin_65k_arithmetic_00
import Theorems.Thm_TaoFivePrimes_sine_bin_65k_arithmetic_01
import Theorems.Thm_TaoFivePrimes_sine_bin_65k_arithmetic_02

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

theorem solution (i : Fin 180) :
    (2*(TaoFivePrimes.sineBinCount65k i.val:ℝ)*
      (4*(TaoFivePrimes.sineBinNumerator65k i.val:ℝ)/10000 + 8/2149 +
        3*(65000+1290*((i.val:ℝ)+1))/2149^2))/
          (65000+1290*(i.val:ℝ))^3 ≤
      (TaoFivePrimes.sineBinTerm65k i.val:ℝ)/10^21 := by
  have hi := i.isLt
  by_cases h0 : i.val < 60
  · have hj : i.val - 0 < 60 := by omega
    let j : Fin 60 := ⟨i.val-0, hj⟩
    have hid : j.val+0 = i.val := by dsimp [j] <;> omega
    have hcast : (j.val:ℝ)+0 = (i.val:ℝ) := by exact_mod_cast hid
    have ht := TaoFivePrimes.sine_bin_65k_arithmetic_00 j
    simpa only [hid,hcast] using ht
  ·
    by_cases h1 : i.val < 120
    · have hj : i.val - 60 < 60 := by omega
      let j : Fin 60 := ⟨i.val-60, hj⟩
      have hid : j.val+60 = i.val := by dsimp [j] <;> omega
      have hcast : (j.val:ℝ)+60 = (i.val:ℝ) := by exact_mod_cast hid
      have ht := TaoFivePrimes.sine_bin_65k_arithmetic_01 j
      simpa only [hid,hcast] using ht
    ·
      have hj : i.val - 120 < 60 := by omega
      let j : Fin 60 := ⟨i.val-120, hj⟩
      have hid : j.val+120 = i.val := by dsimp [j] <;> omega
      have hcast : (j.val:ℝ)+120 = (i.val:ℝ) := by exact_mod_cast hid
      have ht := TaoFivePrimes.sine_bin_65k_arithmetic_02 j
      simpa only [hid,hcast] using ht
