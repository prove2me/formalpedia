-- Prove2me | solution 1 for TaoFivePrimes.theta_cert_blocks_2
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T14:23:05.103458+00:00
-- url     : https://prove2.me/submissions/789748a9-3c6e-4fa1-b506-9d52a7e76113

import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic
import Definitions.Def_TaoFivePrimes_theta_cert_tables
import Theorems.Thm_TaoFivePrimes_theta_cert_plist_eq
import Theorems.Thm_TaoFivePrimes_theta_cert_primesLE_eq
import Theorems.Thm_TaoFivePrimes_theta_cert_clbZ_le_log
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace TaoFivePrimes

open Finset

def plistLit2 : Finset ℕ :=
  ⟨(↑([2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021, 1031, 1033, 1039, 1049, 1051, 1061, 1063, 1069, 1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163, 1171, 1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249, 1259, 1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367, 1373, 1381, 1399, 1409] : List ℕ) : Multiset ℕ), by decide⟩

lemma hplistLit2 : plist = plistLit2 := by decide

lemma blk_17 : ((448 : ℕ) : ℝ) - 2 * Real.sqrt ((448 : ℕ) : ℝ) < Chebyshev.theta ((435 : ℕ) : ℝ) := by
  have hfloor : (42 : ℝ) ≤ 2 * Real.sqrt (448 : ℝ) := by
    have h4 : (42 : ℝ) ^ 2 ≤ 4 * (448 : ℝ) := by norm_num
    have h1 := (Real.le_sqrt (by positivity : (0 : ℝ) ≤ (42 : ℝ))
      (by positivity : (0 : ℝ) ≤ 4 * (448 : ℝ))).mpr h4
    have h2 : Real.sqrt (4 * (448 : ℝ)) = 2 * Real.sqrt (448 : ℝ) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 2) (448 : ℝ),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    rwa [h2] at h1
  have hsT : 42 ≤ 448 := by norm_num
  have hsub : ((448 - 42 : ℕ) : ℝ) = (448 : ℝ) - (42 : ℝ) := by
    rw [Nat.cast_sub hsT]
    norm_num
  have hstep : (448 : ℝ) - 2 * Real.sqrt (448 : ℝ) ≤ ((448 - 42 : ℕ) : ℝ) := by
    rw [hsub]
    linarith [hfloor]
  have hsumI : (448 - 42) * 10 ^ 4 < ∑ p ∈ plist.filter (· ≤ 435), clbZ p := by
    rw [hplistLit2]
    decide
  have hsumR : ((448 - 42 : ℕ) : ℝ) <
      (∑ p ∈ plist.filter (· ≤ 435), (clbZ p : ℝ)) / 10 ^ 4 := by
    have h1 : ((448 - 42 : ℕ) : ℝ) * 10 ^ 4
        < ∑ p ∈ plist.filter (· ≤ 435), (clbZ p : ℝ) := by
      have h2 : ((448 - 42) * 10 ^ 4 : ℕ) < ∑ p ∈ plist.filter (· ≤ 435), clbZ p := hsumI
      exact_mod_cast h2
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
    exact h1
  calc (448 : ℝ) - 2 * Real.sqrt (448 : ℝ) ≤ ((448 - 42 : ℕ) : ℝ) := hstep
    _ < (∑ p ∈ plist.filter (· ≤ 435), (clbZ p : ℝ)) / 10 ^ 4 := hsumR
    _ ≤ ∑ p ∈ plist.filter (· ≤ 435), Real.log p := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
        calc (∑ p ∈ plist.filter (· ≤ 435), (clbZ p : ℝ))
            ≤ ∑ p ∈ plist.filter (· ≤ 435), Real.log p * 10 ^ 4 :=
              Finset.sum_le_sum (fun p hp => theta_cert_clbZ_le_log p (Finset.mem_of_mem_filter p hp))
          _ = (∑ p ∈ plist.filter (· ≤ 435), Real.log p) * 10 ^ 4 := by rw [Finset.sum_mul]
    _ = Chebyshev.theta ((435 : ℕ) : ℝ) := by
        rw [Chebyshev.theta_eq_sum_primesLE_log 435, theta_cert_primesLE_eq 435 (by norm_num)]

lemma blk_18 : ((461 : ℕ) : ℝ) - 2 * Real.sqrt ((461 : ℕ) : ℝ) < Chebyshev.theta ((448 : ℕ) : ℝ) := by
  have hfloor : (42 : ℝ) ≤ 2 * Real.sqrt (461 : ℝ) := by
    have h4 : (42 : ℝ) ^ 2 ≤ 4 * (461 : ℝ) := by norm_num
    have h1 := (Real.le_sqrt (by positivity : (0 : ℝ) ≤ (42 : ℝ))
      (by positivity : (0 : ℝ) ≤ 4 * (461 : ℝ))).mpr h4
    have h2 : Real.sqrt (4 * (461 : ℝ)) = 2 * Real.sqrt (461 : ℝ) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 2) (461 : ℝ),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    rwa [h2] at h1
  have hsT : 42 ≤ 461 := by norm_num
  have hsub : ((461 - 42 : ℕ) : ℝ) = (461 : ℝ) - (42 : ℝ) := by
    rw [Nat.cast_sub hsT]
    norm_num
  have hstep : (461 : ℝ) - 2 * Real.sqrt (461 : ℝ) ≤ ((461 - 42 : ℕ) : ℝ) := by
    rw [hsub]
    linarith [hfloor]
  have hsumI : (461 - 42) * 10 ^ 4 < ∑ p ∈ plist.filter (· ≤ 448), clbZ p := by
    rw [hplistLit2]
    decide
  have hsumR : ((461 - 42 : ℕ) : ℝ) <
      (∑ p ∈ plist.filter (· ≤ 448), (clbZ p : ℝ)) / 10 ^ 4 := by
    have h1 : ((461 - 42 : ℕ) : ℝ) * 10 ^ 4
        < ∑ p ∈ plist.filter (· ≤ 448), (clbZ p : ℝ) := by
      have h2 : ((461 - 42) * 10 ^ 4 : ℕ) < ∑ p ∈ plist.filter (· ≤ 448), clbZ p := hsumI
      exact_mod_cast h2
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
    exact h1
  calc (461 : ℝ) - 2 * Real.sqrt (461 : ℝ) ≤ ((461 - 42 : ℕ) : ℝ) := hstep
    _ < (∑ p ∈ plist.filter (· ≤ 448), (clbZ p : ℝ)) / 10 ^ 4 := hsumR
    _ ≤ ∑ p ∈ plist.filter (· ≤ 448), Real.log p := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
        calc (∑ p ∈ plist.filter (· ≤ 448), (clbZ p : ℝ))
            ≤ ∑ p ∈ plist.filter (· ≤ 448), Real.log p * 10 ^ 4 :=
              Finset.sum_le_sum (fun p hp => theta_cert_clbZ_le_log p (Finset.mem_of_mem_filter p hp))
          _ = (∑ p ∈ plist.filter (· ≤ 448), Real.log p) * 10 ^ 4 := by rw [Finset.sum_mul]
    _ = Chebyshev.theta ((448 : ℕ) : ℝ) := by
        rw [Chebyshev.theta_eq_sum_primesLE_log 448, theta_cert_primesLE_eq 448 (by norm_num)]

lemma blk_19 : ((480 : ℕ) : ℝ) - 2 * Real.sqrt ((480 : ℕ) : ℝ) < Chebyshev.theta ((461 : ℕ) : ℝ) := by
  have hfloor : (43 : ℝ) ≤ 2 * Real.sqrt (480 : ℝ) := by
    have h4 : (43 : ℝ) ^ 2 ≤ 4 * (480 : ℝ) := by norm_num
    have h1 := (Real.le_sqrt (by positivity : (0 : ℝ) ≤ (43 : ℝ))
      (by positivity : (0 : ℝ) ≤ 4 * (480 : ℝ))).mpr h4
    have h2 : Real.sqrt (4 * (480 : ℝ)) = 2 * Real.sqrt (480 : ℝ) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 2) (480 : ℝ),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    rwa [h2] at h1
  have hsT : 43 ≤ 480 := by norm_num
  have hsub : ((480 - 43 : ℕ) : ℝ) = (480 : ℝ) - (43 : ℝ) := by
    rw [Nat.cast_sub hsT]
    norm_num
  have hstep : (480 : ℝ) - 2 * Real.sqrt (480 : ℝ) ≤ ((480 - 43 : ℕ) : ℝ) := by
    rw [hsub]
    linarith [hfloor]
  have hsumI : (480 - 43) * 10 ^ 4 < ∑ p ∈ plist.filter (· ≤ 461), clbZ p := by
    rw [hplistLit2]
    decide
  have hsumR : ((480 - 43 : ℕ) : ℝ) <
      (∑ p ∈ plist.filter (· ≤ 461), (clbZ p : ℝ)) / 10 ^ 4 := by
    have h1 : ((480 - 43 : ℕ) : ℝ) * 10 ^ 4
        < ∑ p ∈ plist.filter (· ≤ 461), (clbZ p : ℝ) := by
      have h2 : ((480 - 43) * 10 ^ 4 : ℕ) < ∑ p ∈ plist.filter (· ≤ 461), clbZ p := hsumI
      exact_mod_cast h2
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
    exact h1
  calc (480 : ℝ) - 2 * Real.sqrt (480 : ℝ) ≤ ((480 - 43 : ℕ) : ℝ) := hstep
    _ < (∑ p ∈ plist.filter (· ≤ 461), (clbZ p : ℝ)) / 10 ^ 4 := hsumR
    _ ≤ ∑ p ∈ plist.filter (· ≤ 461), Real.log p := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
        calc (∑ p ∈ plist.filter (· ≤ 461), (clbZ p : ℝ))
            ≤ ∑ p ∈ plist.filter (· ≤ 461), Real.log p * 10 ^ 4 :=
              Finset.sum_le_sum (fun p hp => theta_cert_clbZ_le_log p (Finset.mem_of_mem_filter p hp))
          _ = (∑ p ∈ plist.filter (· ≤ 461), Real.log p) * 10 ^ 4 := by rw [Finset.sum_mul]
    _ = Chebyshev.theta ((461 : ℕ) : ℝ) := by
        rw [Chebyshev.theta_eq_sum_primesLE_log 461, theta_cert_primesLE_eq 461 (by norm_num)]

lemma blk_20 : ((499 : ℕ) : ℝ) - 2 * Real.sqrt ((499 : ℕ) : ℝ) < Chebyshev.theta ((480 : ℕ) : ℝ) := by
  have hfloor : (44 : ℝ) ≤ 2 * Real.sqrt (499 : ℝ) := by
    have h4 : (44 : ℝ) ^ 2 ≤ 4 * (499 : ℝ) := by norm_num
    have h1 := (Real.le_sqrt (by positivity : (0 : ℝ) ≤ (44 : ℝ))
      (by positivity : (0 : ℝ) ≤ 4 * (499 : ℝ))).mpr h4
    have h2 : Real.sqrt (4 * (499 : ℝ)) = 2 * Real.sqrt (499 : ℝ) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 2) (499 : ℝ),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    rwa [h2] at h1
  have hsT : 44 ≤ 499 := by norm_num
  have hsub : ((499 - 44 : ℕ) : ℝ) = (499 : ℝ) - (44 : ℝ) := by
    rw [Nat.cast_sub hsT]
    norm_num
  have hstep : (499 : ℝ) - 2 * Real.sqrt (499 : ℝ) ≤ ((499 - 44 : ℕ) : ℝ) := by
    rw [hsub]
    linarith [hfloor]
  have hsumI : (499 - 44) * 10 ^ 4 < ∑ p ∈ plist.filter (· ≤ 480), clbZ p := by
    rw [hplistLit2]
    decide
  have hsumR : ((499 - 44 : ℕ) : ℝ) <
      (∑ p ∈ plist.filter (· ≤ 480), (clbZ p : ℝ)) / 10 ^ 4 := by
    have h1 : ((499 - 44 : ℕ) : ℝ) * 10 ^ 4
        < ∑ p ∈ plist.filter (· ≤ 480), (clbZ p : ℝ) := by
      have h2 : ((499 - 44) * 10 ^ 4 : ℕ) < ∑ p ∈ plist.filter (· ≤ 480), clbZ p := hsumI
      exact_mod_cast h2
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
    exact h1
  calc (499 : ℝ) - 2 * Real.sqrt (499 : ℝ) ≤ ((499 - 44 : ℕ) : ℝ) := hstep
    _ < (∑ p ∈ plist.filter (· ≤ 480), (clbZ p : ℝ)) / 10 ^ 4 := hsumR
    _ ≤ ∑ p ∈ plist.filter (· ≤ 480), Real.log p := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
        calc (∑ p ∈ plist.filter (· ≤ 480), (clbZ p : ℝ))
            ≤ ∑ p ∈ plist.filter (· ≤ 480), Real.log p * 10 ^ 4 :=
              Finset.sum_le_sum (fun p hp => theta_cert_clbZ_le_log p (Finset.mem_of_mem_filter p hp))
          _ = (∑ p ∈ plist.filter (· ≤ 480), Real.log p) * 10 ^ 4 := by rw [Finset.sum_mul]
    _ = Chebyshev.theta ((480 : ℕ) : ℝ) := by
        rw [Chebyshev.theta_eq_sum_primesLE_log 480, theta_cert_primesLE_eq 480 (by norm_num)]

lemma blk_21 : ((519 : ℕ) : ℝ) - 2 * Real.sqrt ((519 : ℕ) : ℝ) < Chebyshev.theta ((499 : ℕ) : ℝ) := by
  have hfloor : (45 : ℝ) ≤ 2 * Real.sqrt (519 : ℝ) := by
    have h4 : (45 : ℝ) ^ 2 ≤ 4 * (519 : ℝ) := by norm_num
    have h1 := (Real.le_sqrt (by positivity : (0 : ℝ) ≤ (45 : ℝ))
      (by positivity : (0 : ℝ) ≤ 4 * (519 : ℝ))).mpr h4
    have h2 : Real.sqrt (4 * (519 : ℝ)) = 2 * Real.sqrt (519 : ℝ) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 2) (519 : ℝ),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    rwa [h2] at h1
  have hsT : 45 ≤ 519 := by norm_num
  have hsub : ((519 - 45 : ℕ) : ℝ) = (519 : ℝ) - (45 : ℝ) := by
    rw [Nat.cast_sub hsT]
    norm_num
  have hstep : (519 : ℝ) - 2 * Real.sqrt (519 : ℝ) ≤ ((519 - 45 : ℕ) : ℝ) := by
    rw [hsub]
    linarith [hfloor]
  have hsumI : (519 - 45) * 10 ^ 4 < ∑ p ∈ plist.filter (· ≤ 499), clbZ p := by
    rw [hplistLit2]
    decide
  have hsumR : ((519 - 45 : ℕ) : ℝ) <
      (∑ p ∈ plist.filter (· ≤ 499), (clbZ p : ℝ)) / 10 ^ 4 := by
    have h1 : ((519 - 45 : ℕ) : ℝ) * 10 ^ 4
        < ∑ p ∈ plist.filter (· ≤ 499), (clbZ p : ℝ) := by
      have h2 : ((519 - 45) * 10 ^ 4 : ℕ) < ∑ p ∈ plist.filter (· ≤ 499), clbZ p := hsumI
      exact_mod_cast h2
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
    exact h1
  calc (519 : ℝ) - 2 * Real.sqrt (519 : ℝ) ≤ ((519 - 45 : ℕ) : ℝ) := hstep
    _ < (∑ p ∈ plist.filter (· ≤ 499), (clbZ p : ℝ)) / 10 ^ 4 := hsumR
    _ ≤ ∑ p ∈ plist.filter (· ≤ 499), Real.log p := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
        calc (∑ p ∈ plist.filter (· ≤ 499), (clbZ p : ℝ))
            ≤ ∑ p ∈ plist.filter (· ≤ 499), Real.log p * 10 ^ 4 :=
              Finset.sum_le_sum (fun p hp => theta_cert_clbZ_le_log p (Finset.mem_of_mem_filter p hp))
          _ = (∑ p ∈ plist.filter (· ≤ 499), Real.log p) * 10 ^ 4 := by rw [Finset.sum_mul]
    _ = Chebyshev.theta ((499 : ℕ) : ℝ) := by
        rw [Chebyshev.theta_eq_sum_primesLE_log 499, theta_cert_primesLE_eq 499 (by norm_num)]

lemma blk_22 : ((533 : ℕ) : ℝ) - 2 * Real.sqrt ((533 : ℕ) : ℝ) < Chebyshev.theta ((519 : ℕ) : ℝ) := by
  have hfloor : (46 : ℝ) ≤ 2 * Real.sqrt (533 : ℝ) := by
    have h4 : (46 : ℝ) ^ 2 ≤ 4 * (533 : ℝ) := by norm_num
    have h1 := (Real.le_sqrt (by positivity : (0 : ℝ) ≤ (46 : ℝ))
      (by positivity : (0 : ℝ) ≤ 4 * (533 : ℝ))).mpr h4
    have h2 : Real.sqrt (4 * (533 : ℝ)) = 2 * Real.sqrt (533 : ℝ) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 2) (533 : ℝ),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    rwa [h2] at h1
  have hsT : 46 ≤ 533 := by norm_num
  have hsub : ((533 - 46 : ℕ) : ℝ) = (533 : ℝ) - (46 : ℝ) := by
    rw [Nat.cast_sub hsT]
    norm_num
  have hstep : (533 : ℝ) - 2 * Real.sqrt (533 : ℝ) ≤ ((533 - 46 : ℕ) : ℝ) := by
    rw [hsub]
    linarith [hfloor]
  have hsumI : (533 - 46) * 10 ^ 4 < ∑ p ∈ plist.filter (· ≤ 519), clbZ p := by
    rw [hplistLit2]
    decide
  have hsumR : ((533 - 46 : ℕ) : ℝ) <
      (∑ p ∈ plist.filter (· ≤ 519), (clbZ p : ℝ)) / 10 ^ 4 := by
    have h1 : ((533 - 46 : ℕ) : ℝ) * 10 ^ 4
        < ∑ p ∈ plist.filter (· ≤ 519), (clbZ p : ℝ) := by
      have h2 : ((533 - 46) * 10 ^ 4 : ℕ) < ∑ p ∈ plist.filter (· ≤ 519), clbZ p := hsumI
      exact_mod_cast h2
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
    exact h1
  calc (533 : ℝ) - 2 * Real.sqrt (533 : ℝ) ≤ ((533 - 46 : ℕ) : ℝ) := hstep
    _ < (∑ p ∈ plist.filter (· ≤ 519), (clbZ p : ℝ)) / 10 ^ 4 := hsumR
    _ ≤ ∑ p ∈ plist.filter (· ≤ 519), Real.log p := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
        calc (∑ p ∈ plist.filter (· ≤ 519), (clbZ p : ℝ))
            ≤ ∑ p ∈ plist.filter (· ≤ 519), Real.log p * 10 ^ 4 :=
              Finset.sum_le_sum (fun p hp => theta_cert_clbZ_le_log p (Finset.mem_of_mem_filter p hp))
          _ = (∑ p ∈ plist.filter (· ≤ 519), Real.log p) * 10 ^ 4 := by rw [Finset.sum_mul]
    _ = Chebyshev.theta ((519 : ℕ) : ℝ) := by
        rw [Chebyshev.theta_eq_sum_primesLE_log 519, theta_cert_primesLE_eq 519 (by norm_num)]

lemma blk_23 : ((545 : ℕ) : ℝ) - 2 * Real.sqrt ((545 : ℕ) : ℝ) < Chebyshev.theta ((533 : ℕ) : ℝ) := by
  have hfloor : (46 : ℝ) ≤ 2 * Real.sqrt (545 : ℝ) := by
    have h4 : (46 : ℝ) ^ 2 ≤ 4 * (545 : ℝ) := by norm_num
    have h1 := (Real.le_sqrt (by positivity : (0 : ℝ) ≤ (46 : ℝ))
      (by positivity : (0 : ℝ) ≤ 4 * (545 : ℝ))).mpr h4
    have h2 : Real.sqrt (4 * (545 : ℝ)) = 2 * Real.sqrt (545 : ℝ) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 2) (545 : ℝ),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    rwa [h2] at h1
  have hsT : 46 ≤ 545 := by norm_num
  have hsub : ((545 - 46 : ℕ) : ℝ) = (545 : ℝ) - (46 : ℝ) := by
    rw [Nat.cast_sub hsT]
    norm_num
  have hstep : (545 : ℝ) - 2 * Real.sqrt (545 : ℝ) ≤ ((545 - 46 : ℕ) : ℝ) := by
    rw [hsub]
    linarith [hfloor]
  have hsumI : (545 - 46) * 10 ^ 4 < ∑ p ∈ plist.filter (· ≤ 533), clbZ p := by
    rw [hplistLit2]
    decide
  have hsumR : ((545 - 46 : ℕ) : ℝ) <
      (∑ p ∈ plist.filter (· ≤ 533), (clbZ p : ℝ)) / 10 ^ 4 := by
    have h1 : ((545 - 46 : ℕ) : ℝ) * 10 ^ 4
        < ∑ p ∈ plist.filter (· ≤ 533), (clbZ p : ℝ) := by
      have h2 : ((545 - 46) * 10 ^ 4 : ℕ) < ∑ p ∈ plist.filter (· ≤ 533), clbZ p := hsumI
      exact_mod_cast h2
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
    exact h1
  calc (545 : ℝ) - 2 * Real.sqrt (545 : ℝ) ≤ ((545 - 46 : ℕ) : ℝ) := hstep
    _ < (∑ p ∈ plist.filter (· ≤ 533), (clbZ p : ℝ)) / 10 ^ 4 := hsumR
    _ ≤ ∑ p ∈ plist.filter (· ≤ 533), Real.log p := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
        calc (∑ p ∈ plist.filter (· ≤ 533), (clbZ p : ℝ))
            ≤ ∑ p ∈ plist.filter (· ≤ 533), Real.log p * 10 ^ 4 :=
              Finset.sum_le_sum (fun p hp => theta_cert_clbZ_le_log p (Finset.mem_of_mem_filter p hp))
          _ = (∑ p ∈ plist.filter (· ≤ 533), Real.log p) * 10 ^ 4 := by rw [Finset.sum_mul]
    _ = Chebyshev.theta ((533 : ℕ) : ℝ) := by
        rw [Chebyshev.theta_eq_sum_primesLE_log 533, theta_cert_primesLE_eq 533 (by norm_num)]

lemma blk_24 : ((551 : ℕ) : ℝ) - 2 * Real.sqrt ((551 : ℕ) : ℝ) < Chebyshev.theta ((545 : ℕ) : ℝ) := by
  have hfloor : (46 : ℝ) ≤ 2 * Real.sqrt (551 : ℝ) := by
    have h4 : (46 : ℝ) ^ 2 ≤ 4 * (551 : ℝ) := by norm_num
    have h1 := (Real.le_sqrt (by positivity : (0 : ℝ) ≤ (46 : ℝ))
      (by positivity : (0 : ℝ) ≤ 4 * (551 : ℝ))).mpr h4
    have h2 : Real.sqrt (4 * (551 : ℝ)) = 2 * Real.sqrt (551 : ℝ) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 2) (551 : ℝ),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    rwa [h2] at h1
  have hsT : 46 ≤ 551 := by norm_num
  have hsub : ((551 - 46 : ℕ) : ℝ) = (551 : ℝ) - (46 : ℝ) := by
    rw [Nat.cast_sub hsT]
    norm_num
  have hstep : (551 : ℝ) - 2 * Real.sqrt (551 : ℝ) ≤ ((551 - 46 : ℕ) : ℝ) := by
    rw [hsub]
    linarith [hfloor]
  have hsumI : (551 - 46) * 10 ^ 4 < ∑ p ∈ plist.filter (· ≤ 545), clbZ p := by
    rw [hplistLit2]
    decide
  have hsumR : ((551 - 46 : ℕ) : ℝ) <
      (∑ p ∈ plist.filter (· ≤ 545), (clbZ p : ℝ)) / 10 ^ 4 := by
    have h1 : ((551 - 46 : ℕ) : ℝ) * 10 ^ 4
        < ∑ p ∈ plist.filter (· ≤ 545), (clbZ p : ℝ) := by
      have h2 : ((551 - 46) * 10 ^ 4 : ℕ) < ∑ p ∈ plist.filter (· ≤ 545), clbZ p := hsumI
      exact_mod_cast h2
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
    exact h1
  calc (551 : ℝ) - 2 * Real.sqrt (551 : ℝ) ≤ ((551 - 46 : ℕ) : ℝ) := hstep
    _ < (∑ p ∈ plist.filter (· ≤ 545), (clbZ p : ℝ)) / 10 ^ 4 := hsumR
    _ ≤ ∑ p ∈ plist.filter (· ≤ 545), Real.log p := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
        calc (∑ p ∈ plist.filter (· ≤ 545), (clbZ p : ℝ))
            ≤ ∑ p ∈ plist.filter (· ≤ 545), Real.log p * 10 ^ 4 :=
              Finset.sum_le_sum (fun p hp => theta_cert_clbZ_le_log p (Finset.mem_of_mem_filter p hp))
          _ = (∑ p ∈ plist.filter (· ≤ 545), Real.log p) * 10 ^ 4 := by rw [Finset.sum_mul]
    _ = Chebyshev.theta ((545 : ℕ) : ℝ) := by
        rw [Chebyshev.theta_eq_sum_primesLE_log 545, theta_cert_primesLE_eq 545 (by norm_num)]

lemma blk_25 : ((559 : ℕ) : ℝ) - 2 * Real.sqrt ((559 : ℕ) : ℝ) < Chebyshev.theta ((551 : ℕ) : ℝ) := by
  have hfloor : (47 : ℝ) ≤ 2 * Real.sqrt (559 : ℝ) := by
    have h4 : (47 : ℝ) ^ 2 ≤ 4 * (559 : ℝ) := by norm_num
    have h1 := (Real.le_sqrt (by positivity : (0 : ℝ) ≤ (47 : ℝ))
      (by positivity : (0 : ℝ) ≤ 4 * (559 : ℝ))).mpr h4
    have h2 : Real.sqrt (4 * (559 : ℝ)) = 2 * Real.sqrt (559 : ℝ) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 2) (559 : ℝ),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    rwa [h2] at h1
  have hsT : 47 ≤ 559 := by norm_num
  have hsub : ((559 - 47 : ℕ) : ℝ) = (559 : ℝ) - (47 : ℝ) := by
    rw [Nat.cast_sub hsT]
    norm_num
  have hstep : (559 : ℝ) - 2 * Real.sqrt (559 : ℝ) ≤ ((559 - 47 : ℕ) : ℝ) := by
    rw [hsub]
    linarith [hfloor]
  have hsumI : (559 - 47) * 10 ^ 4 < ∑ p ∈ plist.filter (· ≤ 551), clbZ p := by
    rw [hplistLit2]
    decide
  have hsumR : ((559 - 47 : ℕ) : ℝ) <
      (∑ p ∈ plist.filter (· ≤ 551), (clbZ p : ℝ)) / 10 ^ 4 := by
    have h1 : ((559 - 47 : ℕ) : ℝ) * 10 ^ 4
        < ∑ p ∈ plist.filter (· ≤ 551), (clbZ p : ℝ) := by
      have h2 : ((559 - 47) * 10 ^ 4 : ℕ) < ∑ p ∈ plist.filter (· ≤ 551), clbZ p := hsumI
      exact_mod_cast h2
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
    exact h1
  calc (559 : ℝ) - 2 * Real.sqrt (559 : ℝ) ≤ ((559 - 47 : ℕ) : ℝ) := hstep
    _ < (∑ p ∈ plist.filter (· ≤ 551), (clbZ p : ℝ)) / 10 ^ 4 := hsumR
    _ ≤ ∑ p ∈ plist.filter (· ≤ 551), Real.log p := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
        calc (∑ p ∈ plist.filter (· ≤ 551), (clbZ p : ℝ))
            ≤ ∑ p ∈ plist.filter (· ≤ 551), Real.log p * 10 ^ 4 :=
              Finset.sum_le_sum (fun p hp => theta_cert_clbZ_le_log p (Finset.mem_of_mem_filter p hp))
          _ = (∑ p ∈ plist.filter (· ≤ 551), Real.log p) * 10 ^ 4 := by rw [Finset.sum_mul]
    _ = Chebyshev.theta ((551 : ℕ) : ℝ) := by
        rw [Chebyshev.theta_eq_sum_primesLE_log 551, theta_cert_primesLE_eq 551 (by norm_num)]

lemma blk_26 : ((565 : ℕ) : ℝ) - 2 * Real.sqrt ((565 : ℕ) : ℝ) < Chebyshev.theta ((559 : ℕ) : ℝ) := by
  have hfloor : (47 : ℝ) ≤ 2 * Real.sqrt (565 : ℝ) := by
    have h4 : (47 : ℝ) ^ 2 ≤ 4 * (565 : ℝ) := by norm_num
    have h1 := (Real.le_sqrt (by positivity : (0 : ℝ) ≤ (47 : ℝ))
      (by positivity : (0 : ℝ) ≤ 4 * (565 : ℝ))).mpr h4
    have h2 : Real.sqrt (4 * (565 : ℝ)) = 2 * Real.sqrt (565 : ℝ) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 2) (565 : ℝ),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    rwa [h2] at h1
  have hsT : 47 ≤ 565 := by norm_num
  have hsub : ((565 - 47 : ℕ) : ℝ) = (565 : ℝ) - (47 : ℝ) := by
    rw [Nat.cast_sub hsT]
    norm_num
  have hstep : (565 : ℝ) - 2 * Real.sqrt (565 : ℝ) ≤ ((565 - 47 : ℕ) : ℝ) := by
    rw [hsub]
    linarith [hfloor]
  have hsumI : (565 - 47) * 10 ^ 4 < ∑ p ∈ plist.filter (· ≤ 559), clbZ p := by
    rw [hplistLit2]
    decide
  have hsumR : ((565 - 47 : ℕ) : ℝ) <
      (∑ p ∈ plist.filter (· ≤ 559), (clbZ p : ℝ)) / 10 ^ 4 := by
    have h1 : ((565 - 47 : ℕ) : ℝ) * 10 ^ 4
        < ∑ p ∈ plist.filter (· ≤ 559), (clbZ p : ℝ) := by
      have h2 : ((565 - 47) * 10 ^ 4 : ℕ) < ∑ p ∈ plist.filter (· ≤ 559), clbZ p := hsumI
      exact_mod_cast h2
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
    exact h1
  calc (565 : ℝ) - 2 * Real.sqrt (565 : ℝ) ≤ ((565 - 47 : ℕ) : ℝ) := hstep
    _ < (∑ p ∈ plist.filter (· ≤ 559), (clbZ p : ℝ)) / 10 ^ 4 := hsumR
    _ ≤ ∑ p ∈ plist.filter (· ≤ 559), Real.log p := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
        calc (∑ p ∈ plist.filter (· ≤ 559), (clbZ p : ℝ))
            ≤ ∑ p ∈ plist.filter (· ≤ 559), Real.log p * 10 ^ 4 :=
              Finset.sum_le_sum (fun p hp => theta_cert_clbZ_le_log p (Finset.mem_of_mem_filter p hp))
          _ = (∑ p ∈ plist.filter (· ≤ 559), Real.log p) * 10 ^ 4 := by rw [Finset.sum_mul]
    _ = Chebyshev.theta ((559 : ℕ) : ℝ) := by
        rw [Chebyshev.theta_eq_sum_primesLE_log 559, theta_cert_primesLE_eq 559 (by norm_num)]

lemma blk_27 : ((571 : ℕ) : ℝ) - 2 * Real.sqrt ((571 : ℕ) : ℝ) < Chebyshev.theta ((565 : ℕ) : ℝ) := by
  have hfloor : (47 : ℝ) ≤ 2 * Real.sqrt (571 : ℝ) := by
    have h4 : (47 : ℝ) ^ 2 ≤ 4 * (571 : ℝ) := by norm_num
    have h1 := (Real.le_sqrt (by positivity : (0 : ℝ) ≤ (47 : ℝ))
      (by positivity : (0 : ℝ) ≤ 4 * (571 : ℝ))).mpr h4
    have h2 : Real.sqrt (4 * (571 : ℝ)) = 2 * Real.sqrt (571 : ℝ) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 2) (571 : ℝ),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    rwa [h2] at h1
  have hsT : 47 ≤ 571 := by norm_num
  have hsub : ((571 - 47 : ℕ) : ℝ) = (571 : ℝ) - (47 : ℝ) := by
    rw [Nat.cast_sub hsT]
    norm_num
  have hstep : (571 : ℝ) - 2 * Real.sqrt (571 : ℝ) ≤ ((571 - 47 : ℕ) : ℝ) := by
    rw [hsub]
    linarith [hfloor]
  have hsumI : (571 - 47) * 10 ^ 4 < ∑ p ∈ plist.filter (· ≤ 565), clbZ p := by
    rw [hplistLit2]
    decide
  have hsumR : ((571 - 47 : ℕ) : ℝ) <
      (∑ p ∈ plist.filter (· ≤ 565), (clbZ p : ℝ)) / 10 ^ 4 := by
    have h1 : ((571 - 47 : ℕ) : ℝ) * 10 ^ 4
        < ∑ p ∈ plist.filter (· ≤ 565), (clbZ p : ℝ) := by
      have h2 : ((571 - 47) * 10 ^ 4 : ℕ) < ∑ p ∈ plist.filter (· ≤ 565), clbZ p := hsumI
      exact_mod_cast h2
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
    exact h1
  calc (571 : ℝ) - 2 * Real.sqrt (571 : ℝ) ≤ ((571 - 47 : ℕ) : ℝ) := hstep
    _ < (∑ p ∈ plist.filter (· ≤ 565), (clbZ p : ℝ)) / 10 ^ 4 := hsumR
    _ ≤ ∑ p ∈ plist.filter (· ≤ 565), Real.log p := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
        calc (∑ p ∈ plist.filter (· ≤ 565), (clbZ p : ℝ))
            ≤ ∑ p ∈ plist.filter (· ≤ 565), Real.log p * 10 ^ 4 :=
              Finset.sum_le_sum (fun p hp => theta_cert_clbZ_le_log p (Finset.mem_of_mem_filter p hp))
          _ = (∑ p ∈ plist.filter (· ≤ 565), Real.log p) * 10 ^ 4 := by rw [Finset.sum_mul]
    _ = Chebyshev.theta ((565 : ℕ) : ℝ) := by
        rw [Chebyshev.theta_eq_sum_primesLE_log 565, theta_cert_primesLE_eq 565 (by norm_num)]

lemma blk_28 : ((585 : ℕ) : ℝ) - 2 * Real.sqrt ((585 : ℕ) : ℝ) < Chebyshev.theta ((571 : ℕ) : ℝ) := by
  have hfloor : (48 : ℝ) ≤ 2 * Real.sqrt (585 : ℝ) := by
    have h4 : (48 : ℝ) ^ 2 ≤ 4 * (585 : ℝ) := by norm_num
    have h1 := (Real.le_sqrt (by positivity : (0 : ℝ) ≤ (48 : ℝ))
      (by positivity : (0 : ℝ) ≤ 4 * (585 : ℝ))).mpr h4
    have h2 : Real.sqrt (4 * (585 : ℝ)) = 2 * Real.sqrt (585 : ℝ) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 2) (585 : ℝ),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    rwa [h2] at h1
  have hsT : 48 ≤ 585 := by norm_num
  have hsub : ((585 - 48 : ℕ) : ℝ) = (585 : ℝ) - (48 : ℝ) := by
    rw [Nat.cast_sub hsT]
    norm_num
  have hstep : (585 : ℝ) - 2 * Real.sqrt (585 : ℝ) ≤ ((585 - 48 : ℕ) : ℝ) := by
    rw [hsub]
    linarith [hfloor]
  have hsumI : (585 - 48) * 10 ^ 4 < ∑ p ∈ plist.filter (· ≤ 571), clbZ p := by
    rw [hplistLit2]
    decide
  have hsumR : ((585 - 48 : ℕ) : ℝ) <
      (∑ p ∈ plist.filter (· ≤ 571), (clbZ p : ℝ)) / 10 ^ 4 := by
    have h1 : ((585 - 48 : ℕ) : ℝ) * 10 ^ 4
        < ∑ p ∈ plist.filter (· ≤ 571), (clbZ p : ℝ) := by
      have h2 : ((585 - 48) * 10 ^ 4 : ℕ) < ∑ p ∈ plist.filter (· ≤ 571), clbZ p := hsumI
      exact_mod_cast h2
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
    exact h1
  calc (585 : ℝ) - 2 * Real.sqrt (585 : ℝ) ≤ ((585 - 48 : ℕ) : ℝ) := hstep
    _ < (∑ p ∈ plist.filter (· ≤ 571), (clbZ p : ℝ)) / 10 ^ 4 := hsumR
    _ ≤ ∑ p ∈ plist.filter (· ≤ 571), Real.log p := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
        calc (∑ p ∈ plist.filter (· ≤ 571), (clbZ p : ℝ))
            ≤ ∑ p ∈ plist.filter (· ≤ 571), Real.log p * 10 ^ 4 :=
              Finset.sum_le_sum (fun p hp => theta_cert_clbZ_le_log p (Finset.mem_of_mem_filter p hp))
          _ = (∑ p ∈ plist.filter (· ≤ 571), Real.log p) * 10 ^ 4 := by rw [Finset.sum_mul]
    _ = Chebyshev.theta ((571 : ℕ) : ℝ) := by
        rw [Chebyshev.theta_eq_sum_primesLE_log 571, theta_cert_primesLE_eq 571 (by norm_num)]

lemma blk_29 : ((591 : ℕ) : ℝ) - 2 * Real.sqrt ((591 : ℕ) : ℝ) < Chebyshev.theta ((585 : ℕ) : ℝ) := by
  have hfloor : (48 : ℝ) ≤ 2 * Real.sqrt (591 : ℝ) := by
    have h4 : (48 : ℝ) ^ 2 ≤ 4 * (591 : ℝ) := by norm_num
    have h1 := (Real.le_sqrt (by positivity : (0 : ℝ) ≤ (48 : ℝ))
      (by positivity : (0 : ℝ) ≤ 4 * (591 : ℝ))).mpr h4
    have h2 : Real.sqrt (4 * (591 : ℝ)) = 2 * Real.sqrt (591 : ℝ) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 2) (591 : ℝ),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    rwa [h2] at h1
  have hsT : 48 ≤ 591 := by norm_num
  have hsub : ((591 - 48 : ℕ) : ℝ) = (591 : ℝ) - (48 : ℝ) := by
    rw [Nat.cast_sub hsT]
    norm_num
  have hstep : (591 : ℝ) - 2 * Real.sqrt (591 : ℝ) ≤ ((591 - 48 : ℕ) : ℝ) := by
    rw [hsub]
    linarith [hfloor]
  have hsumI : (591 - 48) * 10 ^ 4 < ∑ p ∈ plist.filter (· ≤ 585), clbZ p := by
    rw [hplistLit2]
    decide
  have hsumR : ((591 - 48 : ℕ) : ℝ) <
      (∑ p ∈ plist.filter (· ≤ 585), (clbZ p : ℝ)) / 10 ^ 4 := by
    have h1 : ((591 - 48 : ℕ) : ℝ) * 10 ^ 4
        < ∑ p ∈ plist.filter (· ≤ 585), (clbZ p : ℝ) := by
      have h2 : ((591 - 48) * 10 ^ 4 : ℕ) < ∑ p ∈ plist.filter (· ≤ 585), clbZ p := hsumI
      exact_mod_cast h2
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
    exact h1
  calc (591 : ℝ) - 2 * Real.sqrt (591 : ℝ) ≤ ((591 - 48 : ℕ) : ℝ) := hstep
    _ < (∑ p ∈ plist.filter (· ≤ 585), (clbZ p : ℝ)) / 10 ^ 4 := hsumR
    _ ≤ ∑ p ∈ plist.filter (· ≤ 585), Real.log p := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
        calc (∑ p ∈ plist.filter (· ≤ 585), (clbZ p : ℝ))
            ≤ ∑ p ∈ plist.filter (· ≤ 585), Real.log p * 10 ^ 4 :=
              Finset.sum_le_sum (fun p hp => theta_cert_clbZ_le_log p (Finset.mem_of_mem_filter p hp))
          _ = (∑ p ∈ plist.filter (· ≤ 585), Real.log p) * 10 ^ 4 := by rw [Finset.sum_mul]
    _ = Chebyshev.theta ((585 : ℕ) : ℝ) := by
        rw [Chebyshev.theta_eq_sum_primesLE_log 585, theta_cert_primesLE_eq 585 (by norm_num)]

lemma blk_30 : ((598 : ℕ) : ℝ) - 2 * Real.sqrt ((598 : ℕ) : ℝ) < Chebyshev.theta ((591 : ℕ) : ℝ) := by
  have hfloor : (48 : ℝ) ≤ 2 * Real.sqrt (598 : ℝ) := by
    have h4 : (48 : ℝ) ^ 2 ≤ 4 * (598 : ℝ) := by norm_num
    have h1 := (Real.le_sqrt (by positivity : (0 : ℝ) ≤ (48 : ℝ))
      (by positivity : (0 : ℝ) ≤ 4 * (598 : ℝ))).mpr h4
    have h2 : Real.sqrt (4 * (598 : ℝ)) = 2 * Real.sqrt (598 : ℝ) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 2) (598 : ℝ),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    rwa [h2] at h1
  have hsT : 48 ≤ 598 := by norm_num
  have hsub : ((598 - 48 : ℕ) : ℝ) = (598 : ℝ) - (48 : ℝ) := by
    rw [Nat.cast_sub hsT]
    norm_num
  have hstep : (598 : ℝ) - 2 * Real.sqrt (598 : ℝ) ≤ ((598 - 48 : ℕ) : ℝ) := by
    rw [hsub]
    linarith [hfloor]
  have hsumI : (598 - 48) * 10 ^ 4 < ∑ p ∈ plist.filter (· ≤ 591), clbZ p := by
    rw [hplistLit2]
    decide
  have hsumR : ((598 - 48 : ℕ) : ℝ) <
      (∑ p ∈ plist.filter (· ≤ 591), (clbZ p : ℝ)) / 10 ^ 4 := by
    have h1 : ((598 - 48 : ℕ) : ℝ) * 10 ^ 4
        < ∑ p ∈ plist.filter (· ≤ 591), (clbZ p : ℝ) := by
      have h2 : ((598 - 48) * 10 ^ 4 : ℕ) < ∑ p ∈ plist.filter (· ≤ 591), clbZ p := hsumI
      exact_mod_cast h2
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
    exact h1
  calc (598 : ℝ) - 2 * Real.sqrt (598 : ℝ) ≤ ((598 - 48 : ℕ) : ℝ) := hstep
    _ < (∑ p ∈ plist.filter (· ≤ 591), (clbZ p : ℝ)) / 10 ^ 4 := hsumR
    _ ≤ ∑ p ∈ plist.filter (· ≤ 591), Real.log p := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
        calc (∑ p ∈ plist.filter (· ≤ 591), (clbZ p : ℝ))
            ≤ ∑ p ∈ plist.filter (· ≤ 591), Real.log p * 10 ^ 4 :=
              Finset.sum_le_sum (fun p hp => theta_cert_clbZ_le_log p (Finset.mem_of_mem_filter p hp))
          _ = (∑ p ∈ plist.filter (· ≤ 591), Real.log p) * 10 ^ 4 := by rw [Finset.sum_mul]
    _ = Chebyshev.theta ((591 : ℕ) : ℝ) := by
        rw [Chebyshev.theta_eq_sum_primesLE_log 591, theta_cert_primesLE_eq 591 (by norm_num)]

lemma blk_31 : ((605 : ℕ) : ℝ) - 2 * Real.sqrt ((605 : ℕ) : ℝ) < Chebyshev.theta ((598 : ℕ) : ℝ) := by
  have hfloor : (49 : ℝ) ≤ 2 * Real.sqrt (605 : ℝ) := by
    have h4 : (49 : ℝ) ^ 2 ≤ 4 * (605 : ℝ) := by norm_num
    have h1 := (Real.le_sqrt (by positivity : (0 : ℝ) ≤ (49 : ℝ))
      (by positivity : (0 : ℝ) ≤ 4 * (605 : ℝ))).mpr h4
    have h2 : Real.sqrt (4 * (605 : ℝ)) = 2 * Real.sqrt (605 : ℝ) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 2) (605 : ℝ),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    rwa [h2] at h1
  have hsT : 49 ≤ 605 := by norm_num
  have hsub : ((605 - 49 : ℕ) : ℝ) = (605 : ℝ) - (49 : ℝ) := by
    rw [Nat.cast_sub hsT]
    norm_num
  have hstep : (605 : ℝ) - 2 * Real.sqrt (605 : ℝ) ≤ ((605 - 49 : ℕ) : ℝ) := by
    rw [hsub]
    linarith [hfloor]
  have hsumI : (605 - 49) * 10 ^ 4 < ∑ p ∈ plist.filter (· ≤ 598), clbZ p := by
    rw [hplistLit2]
    decide
  have hsumR : ((605 - 49 : ℕ) : ℝ) <
      (∑ p ∈ plist.filter (· ≤ 598), (clbZ p : ℝ)) / 10 ^ 4 := by
    have h1 : ((605 - 49 : ℕ) : ℝ) * 10 ^ 4
        < ∑ p ∈ plist.filter (· ≤ 598), (clbZ p : ℝ) := by
      have h2 : ((605 - 49) * 10 ^ 4 : ℕ) < ∑ p ∈ plist.filter (· ≤ 598), clbZ p := hsumI
      exact_mod_cast h2
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
    exact h1
  calc (605 : ℝ) - 2 * Real.sqrt (605 : ℝ) ≤ ((605 - 49 : ℕ) : ℝ) := hstep
    _ < (∑ p ∈ plist.filter (· ≤ 598), (clbZ p : ℝ)) / 10 ^ 4 := hsumR
    _ ≤ ∑ p ∈ plist.filter (· ≤ 598), Real.log p := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
        calc (∑ p ∈ plist.filter (· ≤ 598), (clbZ p : ℝ))
            ≤ ∑ p ∈ plist.filter (· ≤ 598), Real.log p * 10 ^ 4 :=
              Finset.sum_le_sum (fun p hp => theta_cert_clbZ_le_log p (Finset.mem_of_mem_filter p hp))
          _ = (∑ p ∈ plist.filter (· ≤ 598), Real.log p) * 10 ^ 4 := by rw [Finset.sum_mul]
    _ = Chebyshev.theta ((598 : ℕ) : ℝ) := by
        rw [Chebyshev.theta_eq_sum_primesLE_log 598, theta_cert_primesLE_eq 598 (by norm_num)]

lemma blk_32 : ((618 : ℕ) : ℝ) - 2 * Real.sqrt ((618 : ℕ) : ℝ) < Chebyshev.theta ((605 : ℕ) : ℝ) := by
  have hfloor : (49 : ℝ) ≤ 2 * Real.sqrt (618 : ℝ) := by
    have h4 : (49 : ℝ) ^ 2 ≤ 4 * (618 : ℝ) := by norm_num
    have h1 := (Real.le_sqrt (by positivity : (0 : ℝ) ≤ (49 : ℝ))
      (by positivity : (0 : ℝ) ≤ 4 * (618 : ℝ))).mpr h4
    have h2 : Real.sqrt (4 * (618 : ℝ)) = 2 * Real.sqrt (618 : ℝ) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 2) (618 : ℝ),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    rwa [h2] at h1
  have hsT : 49 ≤ 618 := by norm_num
  have hsub : ((618 - 49 : ℕ) : ℝ) = (618 : ℝ) - (49 : ℝ) := by
    rw [Nat.cast_sub hsT]
    norm_num
  have hstep : (618 : ℝ) - 2 * Real.sqrt (618 : ℝ) ≤ ((618 - 49 : ℕ) : ℝ) := by
    rw [hsub]
    linarith [hfloor]
  have hsumI : (618 - 49) * 10 ^ 4 < ∑ p ∈ plist.filter (· ≤ 605), clbZ p := by
    rw [hplistLit2]
    decide
  have hsumR : ((618 - 49 : ℕ) : ℝ) <
      (∑ p ∈ plist.filter (· ≤ 605), (clbZ p : ℝ)) / 10 ^ 4 := by
    have h1 : ((618 - 49 : ℕ) : ℝ) * 10 ^ 4
        < ∑ p ∈ plist.filter (· ≤ 605), (clbZ p : ℝ) := by
      have h2 : ((618 - 49) * 10 ^ 4 : ℕ) < ∑ p ∈ plist.filter (· ≤ 605), clbZ p := hsumI
      exact_mod_cast h2
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
    exact h1
  calc (618 : ℝ) - 2 * Real.sqrt (618 : ℝ) ≤ ((618 - 49 : ℕ) : ℝ) := hstep
    _ < (∑ p ∈ plist.filter (· ≤ 605), (clbZ p : ℝ)) / 10 ^ 4 := hsumR
    _ ≤ ∑ p ∈ plist.filter (· ≤ 605), Real.log p := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
        calc (∑ p ∈ plist.filter (· ≤ 605), (clbZ p : ℝ))
            ≤ ∑ p ∈ plist.filter (· ≤ 605), Real.log p * 10 ^ 4 :=
              Finset.sum_le_sum (fun p hp => theta_cert_clbZ_le_log p (Finset.mem_of_mem_filter p hp))
          _ = (∑ p ∈ plist.filter (· ≤ 605), Real.log p) * 10 ^ 4 := by rw [Finset.sum_mul]
    _ = Chebyshev.theta ((605 : ℕ) : ℝ) := by
        rw [Chebyshev.theta_eq_sum_primesLE_log 605, theta_cert_primesLE_eq 605 (by norm_num)]

lemma blk_33 : ((638 : ℕ) : ℝ) - 2 * Real.sqrt ((638 : ℕ) : ℝ) < Chebyshev.theta ((618 : ℕ) : ℝ) := by
  have hfloor : (50 : ℝ) ≤ 2 * Real.sqrt (638 : ℝ) := by
    have h4 : (50 : ℝ) ^ 2 ≤ 4 * (638 : ℝ) := by norm_num
    have h1 := (Real.le_sqrt (by positivity : (0 : ℝ) ≤ (50 : ℝ))
      (by positivity : (0 : ℝ) ≤ 4 * (638 : ℝ))).mpr h4
    have h2 : Real.sqrt (4 * (638 : ℝ)) = 2 * Real.sqrt (638 : ℝ) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 2) (638 : ℝ),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    rwa [h2] at h1
  have hsT : 50 ≤ 638 := by norm_num
  have hsub : ((638 - 50 : ℕ) : ℝ) = (638 : ℝ) - (50 : ℝ) := by
    rw [Nat.cast_sub hsT]
    norm_num
  have hstep : (638 : ℝ) - 2 * Real.sqrt (638 : ℝ) ≤ ((638 - 50 : ℕ) : ℝ) := by
    rw [hsub]
    linarith [hfloor]
  have hsumI : (638 - 50) * 10 ^ 4 < ∑ p ∈ plist.filter (· ≤ 618), clbZ p := by
    rw [hplistLit2]
    decide
  have hsumR : ((638 - 50 : ℕ) : ℝ) <
      (∑ p ∈ plist.filter (· ≤ 618), (clbZ p : ℝ)) / 10 ^ 4 := by
    have h1 : ((638 - 50 : ℕ) : ℝ) * 10 ^ 4
        < ∑ p ∈ plist.filter (· ≤ 618), (clbZ p : ℝ) := by
      have h2 : ((638 - 50) * 10 ^ 4 : ℕ) < ∑ p ∈ plist.filter (· ≤ 618), clbZ p := hsumI
      exact_mod_cast h2
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
    exact h1
  calc (638 : ℝ) - 2 * Real.sqrt (638 : ℝ) ≤ ((638 - 50 : ℕ) : ℝ) := hstep
    _ < (∑ p ∈ plist.filter (· ≤ 618), (clbZ p : ℝ)) / 10 ^ 4 := hsumR
    _ ≤ ∑ p ∈ plist.filter (· ≤ 618), Real.log p := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
        calc (∑ p ∈ plist.filter (· ≤ 618), (clbZ p : ℝ))
            ≤ ∑ p ∈ plist.filter (· ≤ 618), Real.log p * 10 ^ 4 :=
              Finset.sum_le_sum (fun p hp => theta_cert_clbZ_le_log p (Finset.mem_of_mem_filter p hp))
          _ = (∑ p ∈ plist.filter (· ≤ 618), Real.log p) * 10 ^ 4 := by rw [Finset.sum_mul]
    _ = Chebyshev.theta ((618 : ℕ) : ℝ) := by
        rw [Chebyshev.theta_eq_sum_primesLE_log 618, theta_cert_primesLE_eq 618 (by norm_num)]

lemma blk_34 : ((652 : ℕ) : ℝ) - 2 * Real.sqrt ((652 : ℕ) : ℝ) < Chebyshev.theta ((638 : ℕ) : ℝ) := by
  have hfloor : (51 : ℝ) ≤ 2 * Real.sqrt (652 : ℝ) := by
    have h4 : (51 : ℝ) ^ 2 ≤ 4 * (652 : ℝ) := by norm_num
    have h1 := (Real.le_sqrt (by positivity : (0 : ℝ) ≤ (51 : ℝ))
      (by positivity : (0 : ℝ) ≤ 4 * (652 : ℝ))).mpr h4
    have h2 : Real.sqrt (4 * (652 : ℝ)) = 2 * Real.sqrt (652 : ℝ) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 2) (652 : ℝ),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    rwa [h2] at h1
  have hsT : 51 ≤ 652 := by norm_num
  have hsub : ((652 - 51 : ℕ) : ℝ) = (652 : ℝ) - (51 : ℝ) := by
    rw [Nat.cast_sub hsT]
    norm_num
  have hstep : (652 : ℝ) - 2 * Real.sqrt (652 : ℝ) ≤ ((652 - 51 : ℕ) : ℝ) := by
    rw [hsub]
    linarith [hfloor]
  have hsumI : (652 - 51) * 10 ^ 4 < ∑ p ∈ plist.filter (· ≤ 638), clbZ p := by
    rw [hplistLit2]
    decide
  have hsumR : ((652 - 51 : ℕ) : ℝ) <
      (∑ p ∈ plist.filter (· ≤ 638), (clbZ p : ℝ)) / 10 ^ 4 := by
    have h1 : ((652 - 51 : ℕ) : ℝ) * 10 ^ 4
        < ∑ p ∈ plist.filter (· ≤ 638), (clbZ p : ℝ) := by
      have h2 : ((652 - 51) * 10 ^ 4 : ℕ) < ∑ p ∈ plist.filter (· ≤ 638), clbZ p := hsumI
      exact_mod_cast h2
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
    exact h1
  calc (652 : ℝ) - 2 * Real.sqrt (652 : ℝ) ≤ ((652 - 51 : ℕ) : ℝ) := hstep
    _ < (∑ p ∈ plist.filter (· ≤ 638), (clbZ p : ℝ)) / 10 ^ 4 := hsumR
    _ ≤ ∑ p ∈ plist.filter (· ≤ 638), Real.log p := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
        calc (∑ p ∈ plist.filter (· ≤ 638), (clbZ p : ℝ))
            ≤ ∑ p ∈ plist.filter (· ≤ 638), Real.log p * 10 ^ 4 :=
              Finset.sum_le_sum (fun p hp => theta_cert_clbZ_le_log p (Finset.mem_of_mem_filter p hp))
          _ = (∑ p ∈ plist.filter (· ≤ 638), Real.log p) * 10 ^ 4 := by rw [Finset.sum_mul]
    _ = Chebyshev.theta ((638 : ℕ) : ℝ) := by
        rw [Chebyshev.theta_eq_sum_primesLE_log 638, theta_cert_primesLE_eq 638 (by norm_num)]


theorem solution (ab : ℕ × ℕ) (hab : ab ∈ blk2) :
    ((min (ab.2 + 1) 1420 : ℕ) : ℝ) - 2 * Real.sqrt ((min (ab.2 + 1) 1420 : ℕ) : ℝ) <
      Chebyshev.theta ((ab.1 : ℕ) : ℝ) := by
  have hmem := hab
  simp only [blk2, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals cases h
  all_goals (first | exact blk_17 | exact blk_18 | exact blk_19 | exact blk_20 | exact blk_21 | exact blk_22 | exact blk_23 | exact blk_24 | exact blk_25 | exact blk_26 | exact blk_27 | exact blk_28 | exact blk_29 | exact blk_30 | exact blk_31 | exact blk_32 | exact blk_33 | exact blk_34)

end TaoFivePrimes


open TaoFivePrimes

/-- The verification harness looks for `theorem solution` in the root
namespace, so the namespaced proof above is re-exported at the root. -/
theorem solution (ab : ℕ × ℕ) (hab : ab ∈ blk2) :
    ((min (ab.2 + 1) 1420 : ℕ) : ℝ) - 2 * Real.sqrt ((min (ab.2 + 1) 1420 : ℕ) : ℝ) <
      Chebyshev.theta ((ab.1 : ℕ) : ℝ) :=
  TaoFivePrimes.solution ab hab
