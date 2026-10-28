-- Prove2me | solution 1 for TaoFivePrimes.sine_bin_65000_all
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T22:05:11.868713+00:00
-- url     : https://prove2.me/submissions/9bfbf041-9503-4f7e-b56e-e4a6bca67273

import Definitions.Def_TaoFivePrimes_SineBinData65k
import Definitions.Def_TaoFivePrimes_SineBinArithmetic65k
import Mathlib.Tactic
import Theorems.Thm_TaoFivePrimes_sine_bin_65k_group_00
import Theorems.Thm_TaoFivePrimes_sine_bin_65k_group_01
import Theorems.Thm_TaoFivePrimes_sine_bin_65k_group_02
import Theorems.Thm_TaoFivePrimes_sine_bin_65k_group_03
import Theorems.Thm_TaoFivePrimes_sine_bin_65k_group_04
import Theorems.Thm_TaoFivePrimes_sine_bin_65k_group_05
import Theorems.Thm_TaoFivePrimes_sine_bin_65k_group_06
import Theorems.Thm_TaoFivePrimes_sine_bin_65k_group_07
import Theorems.Thm_TaoFivePrimes_sine_bin_65k_group_08
import Theorems.Thm_TaoFivePrimes_sine_bin_65k_group_09
import Theorems.Thm_TaoFivePrimes_sine_bin_65k_group_10
import Theorems.Thm_TaoFivePrimes_sine_bin_65k_group_11
import Theorems.Thm_TaoFivePrimes_sine_bin_65k_group_12
import Theorems.Thm_TaoFivePrimes_sine_bin_65k_group_13
import Theorems.Thm_TaoFivePrimes_sine_bin_65k_group_14

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

theorem solution (i : Fin 180) (x : ℝ)
    (hx0 : (65000+1290*(i.val:ℝ))/(2*2151) ≤ x)
    (hx1 : x ≤ (65000+1290*(i.val:ℝ)+1290)/(2*2149)) :
    (Real.sin x)^2 ≤ (TaoFivePrimes.sineBinNumerator65k i.val:ℝ)/10000 := by
  have hi := i.isLt
  by_cases h0 : i.val < 12
  · have hj : i.val - 0 < 12 := by omega
    let j : Fin 12 := ⟨i.val-0, hj⟩
    have hid : j.val+0 = i.val := by dsimp [j] <;> omega
    have hcast : (j.val:ℝ)+0 = (i.val:ℝ) := by exact_mod_cast hid
    have hx0' : (65000+1290*((j.val:ℝ)+0))/(2*2151) ≤ x := by
      simpa only [hcast] using hx0
    have hx1' : x ≤ (65000+1290*((j.val:ℝ)+0)+1290)/(2*2149) := by
      simpa only [hcast] using hx1
    have ht := TaoFivePrimes.sine_bin_65k_group_00 j x hx0' hx1'
    simpa only [hid] using ht
  ·
    by_cases h1 : i.val < 24
    · have hj : i.val - 12 < 12 := by omega
      let j : Fin 12 := ⟨i.val-12, hj⟩
      have hid : j.val+12 = i.val := by dsimp [j] <;> omega
      have hcast : (j.val:ℝ)+12 = (i.val:ℝ) := by exact_mod_cast hid
      have hx0' : (65000+1290*((j.val:ℝ)+12))/(2*2151) ≤ x := by
        simpa only [hcast] using hx0
      have hx1' : x ≤ (65000+1290*((j.val:ℝ)+12)+1290)/(2*2149) := by
        simpa only [hcast] using hx1
      have ht := TaoFivePrimes.sine_bin_65k_group_01 j x hx0' hx1'
      simpa only [hid] using ht
    ·
      by_cases h2 : i.val < 36
      · have hj : i.val - 24 < 12 := by omega
        let j : Fin 12 := ⟨i.val-24, hj⟩
        have hid : j.val+24 = i.val := by dsimp [j] <;> omega
        have hcast : (j.val:ℝ)+24 = (i.val:ℝ) := by exact_mod_cast hid
        have hx0' : (65000+1290*((j.val:ℝ)+24))/(2*2151) ≤ x := by
          simpa only [hcast] using hx0
        have hx1' : x ≤ (65000+1290*((j.val:ℝ)+24)+1290)/(2*2149) := by
          simpa only [hcast] using hx1
        have ht := TaoFivePrimes.sine_bin_65k_group_02 j x hx0' hx1'
        simpa only [hid] using ht
      ·
        by_cases h3 : i.val < 48
        · have hj : i.val - 36 < 12 := by omega
          let j : Fin 12 := ⟨i.val-36, hj⟩
          have hid : j.val+36 = i.val := by dsimp [j] <;> omega
          have hcast : (j.val:ℝ)+36 = (i.val:ℝ) := by exact_mod_cast hid
          have hx0' : (65000+1290*((j.val:ℝ)+36))/(2*2151) ≤ x := by
            simpa only [hcast] using hx0
          have hx1' : x ≤ (65000+1290*((j.val:ℝ)+36)+1290)/(2*2149) := by
            simpa only [hcast] using hx1
          have ht := TaoFivePrimes.sine_bin_65k_group_03 j x hx0' hx1'
          simpa only [hid] using ht
        ·
          by_cases h4 : i.val < 60
          · have hj : i.val - 48 < 12 := by omega
            let j : Fin 12 := ⟨i.val-48, hj⟩
            have hid : j.val+48 = i.val := by dsimp [j] <;> omega
            have hcast : (j.val:ℝ)+48 = (i.val:ℝ) := by exact_mod_cast hid
            have hx0' : (65000+1290*((j.val:ℝ)+48))/(2*2151) ≤ x := by
              simpa only [hcast] using hx0
            have hx1' : x ≤ (65000+1290*((j.val:ℝ)+48)+1290)/(2*2149) := by
              simpa only [hcast] using hx1
            have ht := TaoFivePrimes.sine_bin_65k_group_04 j x hx0' hx1'
            simpa only [hid] using ht
          ·
            by_cases h5 : i.val < 72
            · have hj : i.val - 60 < 12 := by omega
              let j : Fin 12 := ⟨i.val-60, hj⟩
              have hid : j.val+60 = i.val := by dsimp [j] <;> omega
              have hcast : (j.val:ℝ)+60 = (i.val:ℝ) := by exact_mod_cast hid
              have hx0' : (65000+1290*((j.val:ℝ)+60))/(2*2151) ≤ x := by
                simpa only [hcast] using hx0
              have hx1' : x ≤ (65000+1290*((j.val:ℝ)+60)+1290)/(2*2149) := by
                simpa only [hcast] using hx1
              have ht := TaoFivePrimes.sine_bin_65k_group_05 j x hx0' hx1'
              simpa only [hid] using ht
            ·
              by_cases h6 : i.val < 84
              · have hj : i.val - 72 < 12 := by omega
                let j : Fin 12 := ⟨i.val-72, hj⟩
                have hid : j.val+72 = i.val := by dsimp [j] <;> omega
                have hcast : (j.val:ℝ)+72 = (i.val:ℝ) := by exact_mod_cast hid
                have hx0' : (65000+1290*((j.val:ℝ)+72))/(2*2151) ≤ x := by
                  simpa only [hcast] using hx0
                have hx1' : x ≤ (65000+1290*((j.val:ℝ)+72)+1290)/(2*2149) := by
                  simpa only [hcast] using hx1
                have ht := TaoFivePrimes.sine_bin_65k_group_06 j x hx0' hx1'
                simpa only [hid] using ht
              ·
                by_cases h7 : i.val < 96
                · have hj : i.val - 84 < 12 := by omega
                  let j : Fin 12 := ⟨i.val-84, hj⟩
                  have hid : j.val+84 = i.val := by dsimp [j] <;> omega
                  have hcast : (j.val:ℝ)+84 = (i.val:ℝ) := by exact_mod_cast hid
                  have hx0' : (65000+1290*((j.val:ℝ)+84))/(2*2151) ≤ x := by
                    simpa only [hcast] using hx0
                  have hx1' : x ≤ (65000+1290*((j.val:ℝ)+84)+1290)/(2*2149) := by
                    simpa only [hcast] using hx1
                  have ht := TaoFivePrimes.sine_bin_65k_group_07 j x hx0' hx1'
                  simpa only [hid] using ht
                ·
                  by_cases h8 : i.val < 108
                  · have hj : i.val - 96 < 12 := by omega
                    let j : Fin 12 := ⟨i.val-96, hj⟩
                    have hid : j.val+96 = i.val := by dsimp [j] <;> omega
                    have hcast : (j.val:ℝ)+96 = (i.val:ℝ) := by exact_mod_cast hid
                    have hx0' : (65000+1290*((j.val:ℝ)+96))/(2*2151) ≤ x := by
                      simpa only [hcast] using hx0
                    have hx1' : x ≤ (65000+1290*((j.val:ℝ)+96)+1290)/(2*2149) := by
                      simpa only [hcast] using hx1
                    have ht := TaoFivePrimes.sine_bin_65k_group_08 j x hx0' hx1'
                    simpa only [hid] using ht
                  ·
                    by_cases h9 : i.val < 120
                    · have hj : i.val - 108 < 12 := by omega
                      let j : Fin 12 := ⟨i.val-108, hj⟩
                      have hid : j.val+108 = i.val := by dsimp [j] <;> omega
                      have hcast : (j.val:ℝ)+108 = (i.val:ℝ) := by exact_mod_cast hid
                      have hx0' : (65000+1290*((j.val:ℝ)+108))/(2*2151) ≤ x := by
                        simpa only [hcast] using hx0
                      have hx1' : x ≤ (65000+1290*((j.val:ℝ)+108)+1290)/(2*2149) := by
                        simpa only [hcast] using hx1
                      have ht := TaoFivePrimes.sine_bin_65k_group_09 j x hx0' hx1'
                      simpa only [hid] using ht
                    ·
                      by_cases h10 : i.val < 132
                      · have hj : i.val - 120 < 12 := by omega
                        let j : Fin 12 := ⟨i.val-120, hj⟩
                        have hid : j.val+120 = i.val := by dsimp [j] <;> omega
                        have hcast : (j.val:ℝ)+120 = (i.val:ℝ) := by exact_mod_cast hid
                        have hx0' : (65000+1290*((j.val:ℝ)+120))/(2*2151) ≤ x := by
                          simpa only [hcast] using hx0
                        have hx1' : x ≤ (65000+1290*((j.val:ℝ)+120)+1290)/(2*2149) := by
                          simpa only [hcast] using hx1
                        have ht := TaoFivePrimes.sine_bin_65k_group_10 j x hx0' hx1'
                        simpa only [hid] using ht
                      ·
                        by_cases h11 : i.val < 144
                        · have hj : i.val - 132 < 12 := by omega
                          let j : Fin 12 := ⟨i.val-132, hj⟩
                          have hid : j.val+132 = i.val := by dsimp [j] <;> omega
                          have hcast : (j.val:ℝ)+132 = (i.val:ℝ) := by exact_mod_cast hid
                          have hx0' : (65000+1290*((j.val:ℝ)+132))/(2*2151) ≤ x := by
                            simpa only [hcast] using hx0
                          have hx1' : x ≤ (65000+1290*((j.val:ℝ)+132)+1290)/(2*2149) := by
                            simpa only [hcast] using hx1
                          have ht := TaoFivePrimes.sine_bin_65k_group_11 j x hx0' hx1'
                          simpa only [hid] using ht
                        ·
                          by_cases h12 : i.val < 156
                          · have hj : i.val - 144 < 12 := by omega
                            let j : Fin 12 := ⟨i.val-144, hj⟩
                            have hid : j.val+144 = i.val := by dsimp [j] <;> omega
                            have hcast : (j.val:ℝ)+144 = (i.val:ℝ) := by exact_mod_cast hid
                            have hx0' : (65000+1290*((j.val:ℝ)+144))/(2*2151) ≤ x := by
                              simpa only [hcast] using hx0
                            have hx1' : x ≤ (65000+1290*((j.val:ℝ)+144)+1290)/(2*2149) := by
                              simpa only [hcast] using hx1
                            have ht := TaoFivePrimes.sine_bin_65k_group_12 j x hx0' hx1'
                            simpa only [hid] using ht
                          ·
                            by_cases h13 : i.val < 168
                            · have hj : i.val - 156 < 12 := by omega
                              let j : Fin 12 := ⟨i.val-156, hj⟩
                              have hid : j.val+156 = i.val := by dsimp [j] <;> omega
                              have hcast : (j.val:ℝ)+156 = (i.val:ℝ) := by exact_mod_cast hid
                              have hx0' : (65000+1290*((j.val:ℝ)+156))/(2*2151) ≤ x := by
                                simpa only [hcast] using hx0
                              have hx1' : x ≤ (65000+1290*((j.val:ℝ)+156)+1290)/(2*2149) := by
                                simpa only [hcast] using hx1
                              have ht := TaoFivePrimes.sine_bin_65k_group_13 j x hx0' hx1'
                              simpa only [hid] using ht
                            ·
                              have hj : i.val - 168 < 12 := by omega
                              let j : Fin 12 := ⟨i.val-168, hj⟩
                              have hid : j.val+168 = i.val := by dsimp [j] <;> omega
                              have hcast : (j.val:ℝ)+168 = (i.val:ℝ) := by exact_mod_cast hid
                              have hx0' : (65000+1290*((j.val:ℝ)+168))/(2*2151) ≤ x := by
                                simpa only [hcast] using hx0
                              have hx1' : x ≤ (65000+1290*((j.val:ℝ)+168)+1290)/(2*2149) := by
                                simpa only [hcast] using hx1
                              have ht := TaoFivePrimes.sine_bin_65k_group_14 j x hx0' hx1'
                              simpa only [hid] using ht
