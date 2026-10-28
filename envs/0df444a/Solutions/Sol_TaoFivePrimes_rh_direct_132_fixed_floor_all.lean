-- Prove2me | solution 1 for TaoFivePrimes.rh_direct_132_fixed_floor_all
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:54:06.201985+00:00
-- url     : https://prove2.me/submissions/7ac69de9-2f65-455b-a520-37c62c840011

import Definitions.Def_TaoFivePrimes_RHDirect132FastNumerator
import Mathlib.Tactic
import Theorems.Thm_TaoFivePrimes_rh_direct_132_fixed_floor_group0
import Theorems.Thm_TaoFivePrimes_rh_direct_132_fixed_floor_group1
import Theorems.Thm_TaoFivePrimes_rh_direct_132_fixed_floor_group2
import Theorems.Thm_TaoFivePrimes_rh_direct_132_fixed_floor_group3
import Theorems.Thm_TaoFivePrimes_rh_direct_132_fixed_floor_group4
import Theorems.Thm_TaoFivePrimes_rh_direct_132_fixed_floor_group5
import Theorems.Thm_TaoFivePrimes_rh_direct_132_fixed_floor_group6
import Theorems.Thm_TaoFivePrimes_rh_direct_132_fixed_floor_group7
import Theorems.Thm_TaoFivePrimes_rh_direct_132_fixed_floor_group8
import Theorems.Thm_TaoFivePrimes_rh_direct_132_fixed_floor_group9
import Theorems.Thm_TaoFivePrimes_rh_direct_132_fixed_floor_group10
import Theorems.Thm_TaoFivePrimes_rh_direct_132_fixed_floor_group11
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem solution (n : ℕ) (hn : n<60) : RHDirect132FastNumerator.floorHolds n := by
  by_cases h0 : n<5
  · have h := TaoFivePrimes.rh_direct_132_fixed_floor_group0 ⟨n,h0⟩
    simpa only [Fin.val_mk,Nat.zero_add] using h
  by_cases h1 : n<10
  · have hge : 5 ≤ n := by omega
    have h := TaoFivePrimes.rh_direct_132_fixed_floor_group1 ⟨n-5,by omega⟩
    simpa only [Fin.val_mk,Nat.add_sub_of_le hge] using h
  by_cases h2 : n<15
  · have hge : 10 ≤ n := by omega
    have h := TaoFivePrimes.rh_direct_132_fixed_floor_group2 ⟨n-10,by omega⟩
    simpa only [Fin.val_mk,Nat.add_sub_of_le hge] using h
  by_cases h3 : n<20
  · have hge : 15 ≤ n := by omega
    have h := TaoFivePrimes.rh_direct_132_fixed_floor_group3 ⟨n-15,by omega⟩
    simpa only [Fin.val_mk,Nat.add_sub_of_le hge] using h
  by_cases h4 : n<25
  · have hge : 20 ≤ n := by omega
    have h := TaoFivePrimes.rh_direct_132_fixed_floor_group4 ⟨n-20,by omega⟩
    simpa only [Fin.val_mk,Nat.add_sub_of_le hge] using h
  by_cases h5 : n<30
  · have hge : 25 ≤ n := by omega
    have h := TaoFivePrimes.rh_direct_132_fixed_floor_group5 ⟨n-25,by omega⟩
    simpa only [Fin.val_mk,Nat.add_sub_of_le hge] using h
  by_cases h6 : n<35
  · have hge : 30 ≤ n := by omega
    have h := TaoFivePrimes.rh_direct_132_fixed_floor_group6 ⟨n-30,by omega⟩
    simpa only [Fin.val_mk,Nat.add_sub_of_le hge] using h
  by_cases h7 : n<40
  · have hge : 35 ≤ n := by omega
    have h := TaoFivePrimes.rh_direct_132_fixed_floor_group7 ⟨n-35,by omega⟩
    simpa only [Fin.val_mk,Nat.add_sub_of_le hge] using h
  by_cases h8 : n<45
  · have hge : 40 ≤ n := by omega
    have h := TaoFivePrimes.rh_direct_132_fixed_floor_group8 ⟨n-40,by omega⟩
    simpa only [Fin.val_mk,Nat.add_sub_of_le hge] using h
  by_cases h9 : n<50
  · have hge : 45 ≤ n := by omega
    have h := TaoFivePrimes.rh_direct_132_fixed_floor_group9 ⟨n-45,by omega⟩
    simpa only [Fin.val_mk,Nat.add_sub_of_le hge] using h
  by_cases h10 : n<55
  · have hge : 50 ≤ n := by omega
    have h := TaoFivePrimes.rh_direct_132_fixed_floor_group10 ⟨n-50,by omega⟩
    simpa only [Fin.val_mk,Nat.add_sub_of_le hge] using h
  · have hge : 55 ≤ n := by omega
    have h := TaoFivePrimes.rh_direct_132_fixed_floor_group11 ⟨n-55,by omega⟩
    simpa only [Fin.val_mk,Nat.add_sub_of_le hge] using h
