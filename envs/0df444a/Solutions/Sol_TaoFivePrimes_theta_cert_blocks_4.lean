-- Prove2me | solution 1 for TaoFivePrimes.theta_cert_blocks_4
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T14:23:08.56264+00:00
-- url     : https://prove2.me/submissions/6967f717-6d76-4925-9b6a-9d8780a37526

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

def plistLit4 : Finset ℕ :=
  ⟨(↑([2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021, 1031, 1033, 1039, 1049, 1051, 1061, 1063, 1069, 1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163, 1171, 1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249, 1259, 1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367, 1373, 1381, 1399, 1409] : List ℕ) : Multiset ℕ), by decide⟩

lemma hplistLit4 : plist = plistLit4 := by decide

lemma blk_53 : ((1019 : ℕ) : ℝ) - 2 * Real.sqrt ((1019 : ℕ) : ℝ) < Chebyshev.theta ((1005 : ℕ) : ℝ) := by
  have hfloor : (63 : ℝ) ≤ 2 * Real.sqrt (1019 : ℝ) := by
    have h4 : (63 : ℝ) ^ 2 ≤ 4 * (1019 : ℝ) := by norm_num
    have h1 := (Real.le_sqrt (by positivity : (0 : ℝ) ≤ (63 : ℝ))
      (by positivity : (0 : ℝ) ≤ 4 * (1019 : ℝ))).mpr h4
    have h2 : Real.sqrt (4 * (1019 : ℝ)) = 2 * Real.sqrt (1019 : ℝ) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 2) (1019 : ℝ),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    rwa [h2] at h1
  have hsT : 63 ≤ 1019 := by norm_num
  have hsub : ((1019 - 63 : ℕ) : ℝ) = (1019 : ℝ) - (63 : ℝ) := by
    rw [Nat.cast_sub hsT]
    norm_num
  have hstep : (1019 : ℝ) - 2 * Real.sqrt (1019 : ℝ) ≤ ((1019 - 63 : ℕ) : ℝ) := by
    rw [hsub]
    linarith [hfloor]
  have hsumI : (1019 - 63) * 10 ^ 4 < ∑ p ∈ plist.filter (· ≤ 1005), clbZ p := by
    rw [hplistLit4]
    decide
  have hsumR : ((1019 - 63 : ℕ) : ℝ) <
      (∑ p ∈ plist.filter (· ≤ 1005), (clbZ p : ℝ)) / 10 ^ 4 := by
    have h1 : ((1019 - 63 : ℕ) : ℝ) * 10 ^ 4
        < ∑ p ∈ plist.filter (· ≤ 1005), (clbZ p : ℝ) := by
      have h2 : ((1019 - 63) * 10 ^ 4 : ℕ) < ∑ p ∈ plist.filter (· ≤ 1005), clbZ p := hsumI
      exact_mod_cast h2
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
    exact h1
  calc (1019 : ℝ) - 2 * Real.sqrt (1019 : ℝ) ≤ ((1019 - 63 : ℕ) : ℝ) := hstep
    _ < (∑ p ∈ plist.filter (· ≤ 1005), (clbZ p : ℝ)) / 10 ^ 4 := hsumR
    _ ≤ ∑ p ∈ plist.filter (· ≤ 1005), Real.log p := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
        calc (∑ p ∈ plist.filter (· ≤ 1005), (clbZ p : ℝ))
            ≤ ∑ p ∈ plist.filter (· ≤ 1005), Real.log p * 10 ^ 4 :=
              Finset.sum_le_sum (fun p hp => theta_cert_clbZ_le_log p (Finset.mem_of_mem_filter p hp))
          _ = (∑ p ∈ plist.filter (· ≤ 1005), Real.log p) * 10 ^ 4 := by rw [Finset.sum_mul]
    _ = Chebyshev.theta ((1005 : ℕ) : ℝ) := by
        rw [Chebyshev.theta_eq_sum_primesLE_log 1005, theta_cert_primesLE_eq 1005 (by norm_num)]

lemma blk_54 : ((1041 : ℕ) : ℝ) - 2 * Real.sqrt ((1041 : ℕ) : ℝ) < Chebyshev.theta ((1019 : ℕ) : ℝ) := by
  have hfloor : (64 : ℝ) ≤ 2 * Real.sqrt (1041 : ℝ) := by
    have h4 : (64 : ℝ) ^ 2 ≤ 4 * (1041 : ℝ) := by norm_num
    have h1 := (Real.le_sqrt (by positivity : (0 : ℝ) ≤ (64 : ℝ))
      (by positivity : (0 : ℝ) ≤ 4 * (1041 : ℝ))).mpr h4
    have h2 : Real.sqrt (4 * (1041 : ℝ)) = 2 * Real.sqrt (1041 : ℝ) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 2) (1041 : ℝ),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    rwa [h2] at h1
  have hsT : 64 ≤ 1041 := by norm_num
  have hsub : ((1041 - 64 : ℕ) : ℝ) = (1041 : ℝ) - (64 : ℝ) := by
    rw [Nat.cast_sub hsT]
    norm_num
  have hstep : (1041 : ℝ) - 2 * Real.sqrt (1041 : ℝ) ≤ ((1041 - 64 : ℕ) : ℝ) := by
    rw [hsub]
    linarith [hfloor]
  have hsumI : (1041 - 64) * 10 ^ 4 < ∑ p ∈ plist.filter (· ≤ 1019), clbZ p := by
    rw [hplistLit4]
    decide
  have hsumR : ((1041 - 64 : ℕ) : ℝ) <
      (∑ p ∈ plist.filter (· ≤ 1019), (clbZ p : ℝ)) / 10 ^ 4 := by
    have h1 : ((1041 - 64 : ℕ) : ℝ) * 10 ^ 4
        < ∑ p ∈ plist.filter (· ≤ 1019), (clbZ p : ℝ) := by
      have h2 : ((1041 - 64) * 10 ^ 4 : ℕ) < ∑ p ∈ plist.filter (· ≤ 1019), clbZ p := hsumI
      exact_mod_cast h2
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
    exact h1
  calc (1041 : ℝ) - 2 * Real.sqrt (1041 : ℝ) ≤ ((1041 - 64 : ℕ) : ℝ) := hstep
    _ < (∑ p ∈ plist.filter (· ≤ 1019), (clbZ p : ℝ)) / 10 ^ 4 := hsumR
    _ ≤ ∑ p ∈ plist.filter (· ≤ 1019), Real.log p := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
        calc (∑ p ∈ plist.filter (· ≤ 1019), (clbZ p : ℝ))
            ≤ ∑ p ∈ plist.filter (· ≤ 1019), Real.log p * 10 ^ 4 :=
              Finset.sum_le_sum (fun p hp => theta_cert_clbZ_le_log p (Finset.mem_of_mem_filter p hp))
          _ = (∑ p ∈ plist.filter (· ≤ 1019), Real.log p) * 10 ^ 4 := by rw [Finset.sum_mul]
    _ = Chebyshev.theta ((1019 : ℕ) : ℝ) := by
        rw [Chebyshev.theta_eq_sum_primesLE_log 1019, theta_cert_primesLE_eq 1019 (by norm_num)]

lemma blk_55 : ((1069 : ℕ) : ℝ) - 2 * Real.sqrt ((1069 : ℕ) : ℝ) < Chebyshev.theta ((1041 : ℕ) : ℝ) := by
  have hfloor : (65 : ℝ) ≤ 2 * Real.sqrt (1069 : ℝ) := by
    have h4 : (65 : ℝ) ^ 2 ≤ 4 * (1069 : ℝ) := by norm_num
    have h1 := (Real.le_sqrt (by positivity : (0 : ℝ) ≤ (65 : ℝ))
      (by positivity : (0 : ℝ) ≤ 4 * (1069 : ℝ))).mpr h4
    have h2 : Real.sqrt (4 * (1069 : ℝ)) = 2 * Real.sqrt (1069 : ℝ) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 2) (1069 : ℝ),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    rwa [h2] at h1
  have hsT : 65 ≤ 1069 := by norm_num
  have hsub : ((1069 - 65 : ℕ) : ℝ) = (1069 : ℝ) - (65 : ℝ) := by
    rw [Nat.cast_sub hsT]
    norm_num
  have hstep : (1069 : ℝ) - 2 * Real.sqrt (1069 : ℝ) ≤ ((1069 - 65 : ℕ) : ℝ) := by
    rw [hsub]
    linarith [hfloor]
  have hsumI : (1069 - 65) * 10 ^ 4 < ∑ p ∈ plist.filter (· ≤ 1041), clbZ p := by
    rw [hplistLit4]
    decide
  have hsumR : ((1069 - 65 : ℕ) : ℝ) <
      (∑ p ∈ plist.filter (· ≤ 1041), (clbZ p : ℝ)) / 10 ^ 4 := by
    have h1 : ((1069 - 65 : ℕ) : ℝ) * 10 ^ 4
        < ∑ p ∈ plist.filter (· ≤ 1041), (clbZ p : ℝ) := by
      have h2 : ((1069 - 65) * 10 ^ 4 : ℕ) < ∑ p ∈ plist.filter (· ≤ 1041), clbZ p := hsumI
      exact_mod_cast h2
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
    exact h1
  calc (1069 : ℝ) - 2 * Real.sqrt (1069 : ℝ) ≤ ((1069 - 65 : ℕ) : ℝ) := hstep
    _ < (∑ p ∈ plist.filter (· ≤ 1041), (clbZ p : ℝ)) / 10 ^ 4 := hsumR
    _ ≤ ∑ p ∈ plist.filter (· ≤ 1041), Real.log p := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
        calc (∑ p ∈ plist.filter (· ≤ 1041), (clbZ p : ℝ))
            ≤ ∑ p ∈ plist.filter (· ≤ 1041), Real.log p * 10 ^ 4 :=
              Finset.sum_le_sum (fun p hp => theta_cert_clbZ_le_log p (Finset.mem_of_mem_filter p hp))
          _ = (∑ p ∈ plist.filter (· ≤ 1041), Real.log p) * 10 ^ 4 := by rw [Finset.sum_mul]
    _ = Chebyshev.theta ((1041 : ℕ) : ℝ) := by
        rw [Chebyshev.theta_eq_sum_primesLE_log 1041, theta_cert_primesLE_eq 1041 (by norm_num)]

lemma blk_56 : ((1105 : ℕ) : ℝ) - 2 * Real.sqrt ((1105 : ℕ) : ℝ) < Chebyshev.theta ((1069 : ℕ) : ℝ) := by
  have hfloor : (66 : ℝ) ≤ 2 * Real.sqrt (1105 : ℝ) := by
    have h4 : (66 : ℝ) ^ 2 ≤ 4 * (1105 : ℝ) := by norm_num
    have h1 := (Real.le_sqrt (by positivity : (0 : ℝ) ≤ (66 : ℝ))
      (by positivity : (0 : ℝ) ≤ 4 * (1105 : ℝ))).mpr h4
    have h2 : Real.sqrt (4 * (1105 : ℝ)) = 2 * Real.sqrt (1105 : ℝ) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 2) (1105 : ℝ),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    rwa [h2] at h1
  have hsT : 66 ≤ 1105 := by norm_num
  have hsub : ((1105 - 66 : ℕ) : ℝ) = (1105 : ℝ) - (66 : ℝ) := by
    rw [Nat.cast_sub hsT]
    norm_num
  have hstep : (1105 : ℝ) - 2 * Real.sqrt (1105 : ℝ) ≤ ((1105 - 66 : ℕ) : ℝ) := by
    rw [hsub]
    linarith [hfloor]
  have hsumI : (1105 - 66) * 10 ^ 4 < ∑ p ∈ plist.filter (· ≤ 1069), clbZ p := by
    rw [hplistLit4]
    decide
  have hsumR : ((1105 - 66 : ℕ) : ℝ) <
      (∑ p ∈ plist.filter (· ≤ 1069), (clbZ p : ℝ)) / 10 ^ 4 := by
    have h1 : ((1105 - 66 : ℕ) : ℝ) * 10 ^ 4
        < ∑ p ∈ plist.filter (· ≤ 1069), (clbZ p : ℝ) := by
      have h2 : ((1105 - 66) * 10 ^ 4 : ℕ) < ∑ p ∈ plist.filter (· ≤ 1069), clbZ p := hsumI
      exact_mod_cast h2
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
    exact h1
  calc (1105 : ℝ) - 2 * Real.sqrt (1105 : ℝ) ≤ ((1105 - 66 : ℕ) : ℝ) := hstep
    _ < (∑ p ∈ plist.filter (· ≤ 1069), (clbZ p : ℝ)) / 10 ^ 4 := hsumR
    _ ≤ ∑ p ∈ plist.filter (· ≤ 1069), Real.log p := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
        calc (∑ p ∈ plist.filter (· ≤ 1069), (clbZ p : ℝ))
            ≤ ∑ p ∈ plist.filter (· ≤ 1069), Real.log p * 10 ^ 4 :=
              Finset.sum_le_sum (fun p hp => theta_cert_clbZ_le_log p (Finset.mem_of_mem_filter p hp))
          _ = (∑ p ∈ plist.filter (· ≤ 1069), Real.log p) * 10 ^ 4 := by rw [Finset.sum_mul]
    _ = Chebyshev.theta ((1069 : ℕ) : ℝ) := by
        rw [Chebyshev.theta_eq_sum_primesLE_log 1069, theta_cert_primesLE_eq 1069 (by norm_num)]

lemma blk_57 : ((1141 : ℕ) : ℝ) - 2 * Real.sqrt ((1141 : ℕ) : ℝ) < Chebyshev.theta ((1105 : ℕ) : ℝ) := by
  have hfloor : (67 : ℝ) ≤ 2 * Real.sqrt (1141 : ℝ) := by
    have h4 : (67 : ℝ) ^ 2 ≤ 4 * (1141 : ℝ) := by norm_num
    have h1 := (Real.le_sqrt (by positivity : (0 : ℝ) ≤ (67 : ℝ))
      (by positivity : (0 : ℝ) ≤ 4 * (1141 : ℝ))).mpr h4
    have h2 : Real.sqrt (4 * (1141 : ℝ)) = 2 * Real.sqrt (1141 : ℝ) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 2) (1141 : ℝ),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    rwa [h2] at h1
  have hsT : 67 ≤ 1141 := by norm_num
  have hsub : ((1141 - 67 : ℕ) : ℝ) = (1141 : ℝ) - (67 : ℝ) := by
    rw [Nat.cast_sub hsT]
    norm_num
  have hstep : (1141 : ℝ) - 2 * Real.sqrt (1141 : ℝ) ≤ ((1141 - 67 : ℕ) : ℝ) := by
    rw [hsub]
    linarith [hfloor]
  have hsumI : (1141 - 67) * 10 ^ 4 < ∑ p ∈ plist.filter (· ≤ 1105), clbZ p := by
    rw [hplistLit4]
    decide
  have hsumR : ((1141 - 67 : ℕ) : ℝ) <
      (∑ p ∈ plist.filter (· ≤ 1105), (clbZ p : ℝ)) / 10 ^ 4 := by
    have h1 : ((1141 - 67 : ℕ) : ℝ) * 10 ^ 4
        < ∑ p ∈ plist.filter (· ≤ 1105), (clbZ p : ℝ) := by
      have h2 : ((1141 - 67) * 10 ^ 4 : ℕ) < ∑ p ∈ plist.filter (· ≤ 1105), clbZ p := hsumI
      exact_mod_cast h2
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
    exact h1
  calc (1141 : ℝ) - 2 * Real.sqrt (1141 : ℝ) ≤ ((1141 - 67 : ℕ) : ℝ) := hstep
    _ < (∑ p ∈ plist.filter (· ≤ 1105), (clbZ p : ℝ)) / 10 ^ 4 := hsumR
    _ ≤ ∑ p ∈ plist.filter (· ≤ 1105), Real.log p := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
        calc (∑ p ∈ plist.filter (· ≤ 1105), (clbZ p : ℝ))
            ≤ ∑ p ∈ plist.filter (· ≤ 1105), Real.log p * 10 ^ 4 :=
              Finset.sum_le_sum (fun p hp => theta_cert_clbZ_le_log p (Finset.mem_of_mem_filter p hp))
          _ = (∑ p ∈ plist.filter (· ≤ 1105), Real.log p) * 10 ^ 4 := by rw [Finset.sum_mul]
    _ = Chebyshev.theta ((1105 : ℕ) : ℝ) := by
        rw [Chebyshev.theta_eq_sum_primesLE_log 1105, theta_cert_primesLE_eq 1105 (by norm_num)]

lemma blk_58 : ((1170 : ℕ) : ℝ) - 2 * Real.sqrt ((1170 : ℕ) : ℝ) < Chebyshev.theta ((1141 : ℕ) : ℝ) := by
  have hfloor : (68 : ℝ) ≤ 2 * Real.sqrt (1170 : ℝ) := by
    have h4 : (68 : ℝ) ^ 2 ≤ 4 * (1170 : ℝ) := by norm_num
    have h1 := (Real.le_sqrt (by positivity : (0 : ℝ) ≤ (68 : ℝ))
      (by positivity : (0 : ℝ) ≤ 4 * (1170 : ℝ))).mpr h4
    have h2 : Real.sqrt (4 * (1170 : ℝ)) = 2 * Real.sqrt (1170 : ℝ) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 2) (1170 : ℝ),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    rwa [h2] at h1
  have hsT : 68 ≤ 1170 := by norm_num
  have hsub : ((1170 - 68 : ℕ) : ℝ) = (1170 : ℝ) - (68 : ℝ) := by
    rw [Nat.cast_sub hsT]
    norm_num
  have hstep : (1170 : ℝ) - 2 * Real.sqrt (1170 : ℝ) ≤ ((1170 - 68 : ℕ) : ℝ) := by
    rw [hsub]
    linarith [hfloor]
  have hsumI : (1170 - 68) * 10 ^ 4 < ∑ p ∈ plist.filter (· ≤ 1141), clbZ p := by
    rw [hplistLit4]
    decide
  have hsumR : ((1170 - 68 : ℕ) : ℝ) <
      (∑ p ∈ plist.filter (· ≤ 1141), (clbZ p : ℝ)) / 10 ^ 4 := by
    have h1 : ((1170 - 68 : ℕ) : ℝ) * 10 ^ 4
        < ∑ p ∈ plist.filter (· ≤ 1141), (clbZ p : ℝ) := by
      have h2 : ((1170 - 68) * 10 ^ 4 : ℕ) < ∑ p ∈ plist.filter (· ≤ 1141), clbZ p := hsumI
      exact_mod_cast h2
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
    exact h1
  calc (1170 : ℝ) - 2 * Real.sqrt (1170 : ℝ) ≤ ((1170 - 68 : ℕ) : ℝ) := hstep
    _ < (∑ p ∈ plist.filter (· ≤ 1141), (clbZ p : ℝ)) / 10 ^ 4 := hsumR
    _ ≤ ∑ p ∈ plist.filter (· ≤ 1141), Real.log p := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
        calc (∑ p ∈ plist.filter (· ≤ 1141), (clbZ p : ℝ))
            ≤ ∑ p ∈ plist.filter (· ≤ 1141), Real.log p * 10 ^ 4 :=
              Finset.sum_le_sum (fun p hp => theta_cert_clbZ_le_log p (Finset.mem_of_mem_filter p hp))
          _ = (∑ p ∈ plist.filter (· ≤ 1141), Real.log p) * 10 ^ 4 := by rw [Finset.sum_mul]
    _ = Chebyshev.theta ((1141 : ℕ) : ℝ) := by
        rw [Chebyshev.theta_eq_sum_primesLE_log 1141, theta_cert_primesLE_eq 1141 (by norm_num)]

lemma blk_59 : ((1192 : ℕ) : ℝ) - 2 * Real.sqrt ((1192 : ℕ) : ℝ) < Chebyshev.theta ((1170 : ℕ) : ℝ) := by
  have hfloor : (69 : ℝ) ≤ 2 * Real.sqrt (1192 : ℝ) := by
    have h4 : (69 : ℝ) ^ 2 ≤ 4 * (1192 : ℝ) := by norm_num
    have h1 := (Real.le_sqrt (by positivity : (0 : ℝ) ≤ (69 : ℝ))
      (by positivity : (0 : ℝ) ≤ 4 * (1192 : ℝ))).mpr h4
    have h2 : Real.sqrt (4 * (1192 : ℝ)) = 2 * Real.sqrt (1192 : ℝ) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 2) (1192 : ℝ),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    rwa [h2] at h1
  have hsT : 69 ≤ 1192 := by norm_num
  have hsub : ((1192 - 69 : ℕ) : ℝ) = (1192 : ℝ) - (69 : ℝ) := by
    rw [Nat.cast_sub hsT]
    norm_num
  have hstep : (1192 : ℝ) - 2 * Real.sqrt (1192 : ℝ) ≤ ((1192 - 69 : ℕ) : ℝ) := by
    rw [hsub]
    linarith [hfloor]
  have hsumI : (1192 - 69) * 10 ^ 4 < ∑ p ∈ plist.filter (· ≤ 1170), clbZ p := by
    rw [hplistLit4]
    decide
  have hsumR : ((1192 - 69 : ℕ) : ℝ) <
      (∑ p ∈ plist.filter (· ≤ 1170), (clbZ p : ℝ)) / 10 ^ 4 := by
    have h1 : ((1192 - 69 : ℕ) : ℝ) * 10 ^ 4
        < ∑ p ∈ plist.filter (· ≤ 1170), (clbZ p : ℝ) := by
      have h2 : ((1192 - 69) * 10 ^ 4 : ℕ) < ∑ p ∈ plist.filter (· ≤ 1170), clbZ p := hsumI
      exact_mod_cast h2
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
    exact h1
  calc (1192 : ℝ) - 2 * Real.sqrt (1192 : ℝ) ≤ ((1192 - 69 : ℕ) : ℝ) := hstep
    _ < (∑ p ∈ plist.filter (· ≤ 1170), (clbZ p : ℝ)) / 10 ^ 4 := hsumR
    _ ≤ ∑ p ∈ plist.filter (· ≤ 1170), Real.log p := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
        calc (∑ p ∈ plist.filter (· ≤ 1170), (clbZ p : ℝ))
            ≤ ∑ p ∈ plist.filter (· ≤ 1170), Real.log p * 10 ^ 4 :=
              Finset.sum_le_sum (fun p hp => theta_cert_clbZ_le_log p (Finset.mem_of_mem_filter p hp))
          _ = (∑ p ∈ plist.filter (· ≤ 1170), Real.log p) * 10 ^ 4 := by rw [Finset.sum_mul]
    _ = Chebyshev.theta ((1170 : ℕ) : ℝ) := by
        rw [Chebyshev.theta_eq_sum_primesLE_log 1170, theta_cert_primesLE_eq 1170 (by norm_num)]

lemma blk_60 : ((1214 : ℕ) : ℝ) - 2 * Real.sqrt ((1214 : ℕ) : ℝ) < Chebyshev.theta ((1192 : ℕ) : ℝ) := by
  have hfloor : (69 : ℝ) ≤ 2 * Real.sqrt (1214 : ℝ) := by
    have h4 : (69 : ℝ) ^ 2 ≤ 4 * (1214 : ℝ) := by norm_num
    have h1 := (Real.le_sqrt (by positivity : (0 : ℝ) ≤ (69 : ℝ))
      (by positivity : (0 : ℝ) ≤ 4 * (1214 : ℝ))).mpr h4
    have h2 : Real.sqrt (4 * (1214 : ℝ)) = 2 * Real.sqrt (1214 : ℝ) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 2) (1214 : ℝ),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    rwa [h2] at h1
  have hsT : 69 ≤ 1214 := by norm_num
  have hsub : ((1214 - 69 : ℕ) : ℝ) = (1214 : ℝ) - (69 : ℝ) := by
    rw [Nat.cast_sub hsT]
    norm_num
  have hstep : (1214 : ℝ) - 2 * Real.sqrt (1214 : ℝ) ≤ ((1214 - 69 : ℕ) : ℝ) := by
    rw [hsub]
    linarith [hfloor]
  have hsumI : (1214 - 69) * 10 ^ 4 < ∑ p ∈ plist.filter (· ≤ 1192), clbZ p := by
    rw [hplistLit4]
    decide
  have hsumR : ((1214 - 69 : ℕ) : ℝ) <
      (∑ p ∈ plist.filter (· ≤ 1192), (clbZ p : ℝ)) / 10 ^ 4 := by
    have h1 : ((1214 - 69 : ℕ) : ℝ) * 10 ^ 4
        < ∑ p ∈ plist.filter (· ≤ 1192), (clbZ p : ℝ) := by
      have h2 : ((1214 - 69) * 10 ^ 4 : ℕ) < ∑ p ∈ plist.filter (· ≤ 1192), clbZ p := hsumI
      exact_mod_cast h2
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
    exact h1
  calc (1214 : ℝ) - 2 * Real.sqrt (1214 : ℝ) ≤ ((1214 - 69 : ℕ) : ℝ) := hstep
    _ < (∑ p ∈ plist.filter (· ≤ 1192), (clbZ p : ℝ)) / 10 ^ 4 := hsumR
    _ ≤ ∑ p ∈ plist.filter (· ≤ 1192), Real.log p := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
        calc (∑ p ∈ plist.filter (· ≤ 1192), (clbZ p : ℝ))
            ≤ ∑ p ∈ plist.filter (· ≤ 1192), Real.log p * 10 ^ 4 :=
              Finset.sum_le_sum (fun p hp => theta_cert_clbZ_le_log p (Finset.mem_of_mem_filter p hp))
          _ = (∑ p ∈ plist.filter (· ≤ 1192), Real.log p) * 10 ^ 4 := by rw [Finset.sum_mul]
    _ = Chebyshev.theta ((1192 : ℕ) : ℝ) := by
        rw [Chebyshev.theta_eq_sum_primesLE_log 1192, theta_cert_primesLE_eq 1192 (by norm_num)]

lemma blk_61 : ((1236 : ℕ) : ℝ) - 2 * Real.sqrt ((1236 : ℕ) : ℝ) < Chebyshev.theta ((1214 : ℕ) : ℝ) := by
  have hfloor : (70 : ℝ) ≤ 2 * Real.sqrt (1236 : ℝ) := by
    have h4 : (70 : ℝ) ^ 2 ≤ 4 * (1236 : ℝ) := by norm_num
    have h1 := (Real.le_sqrt (by positivity : (0 : ℝ) ≤ (70 : ℝ))
      (by positivity : (0 : ℝ) ≤ 4 * (1236 : ℝ))).mpr h4
    have h2 : Real.sqrt (4 * (1236 : ℝ)) = 2 * Real.sqrt (1236 : ℝ) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 2) (1236 : ℝ),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    rwa [h2] at h1
  have hsT : 70 ≤ 1236 := by norm_num
  have hsub : ((1236 - 70 : ℕ) : ℝ) = (1236 : ℝ) - (70 : ℝ) := by
    rw [Nat.cast_sub hsT]
    norm_num
  have hstep : (1236 : ℝ) - 2 * Real.sqrt (1236 : ℝ) ≤ ((1236 - 70 : ℕ) : ℝ) := by
    rw [hsub]
    linarith [hfloor]
  have hsumI : (1236 - 70) * 10 ^ 4 < ∑ p ∈ plist.filter (· ≤ 1214), clbZ p := by
    rw [hplistLit4]
    decide
  have hsumR : ((1236 - 70 : ℕ) : ℝ) <
      (∑ p ∈ plist.filter (· ≤ 1214), (clbZ p : ℝ)) / 10 ^ 4 := by
    have h1 : ((1236 - 70 : ℕ) : ℝ) * 10 ^ 4
        < ∑ p ∈ plist.filter (· ≤ 1214), (clbZ p : ℝ) := by
      have h2 : ((1236 - 70) * 10 ^ 4 : ℕ) < ∑ p ∈ plist.filter (· ≤ 1214), clbZ p := hsumI
      exact_mod_cast h2
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
    exact h1
  calc (1236 : ℝ) - 2 * Real.sqrt (1236 : ℝ) ≤ ((1236 - 70 : ℕ) : ℝ) := hstep
    _ < (∑ p ∈ plist.filter (· ≤ 1214), (clbZ p : ℝ)) / 10 ^ 4 := hsumR
    _ ≤ ∑ p ∈ plist.filter (· ≤ 1214), Real.log p := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
        calc (∑ p ∈ plist.filter (· ≤ 1214), (clbZ p : ℝ))
            ≤ ∑ p ∈ plist.filter (· ≤ 1214), Real.log p * 10 ^ 4 :=
              Finset.sum_le_sum (fun p hp => theta_cert_clbZ_le_log p (Finset.mem_of_mem_filter p hp))
          _ = (∑ p ∈ plist.filter (· ≤ 1214), Real.log p) * 10 ^ 4 := by rw [Finset.sum_mul]
    _ = Chebyshev.theta ((1214 : ℕ) : ℝ) := by
        rw [Chebyshev.theta_eq_sum_primesLE_log 1214, theta_cert_primesLE_eq 1214 (by norm_num)]

lemma blk_62 : ((1265 : ℕ) : ℝ) - 2 * Real.sqrt ((1265 : ℕ) : ℝ) < Chebyshev.theta ((1236 : ℕ) : ℝ) := by
  have hfloor : (71 : ℝ) ≤ 2 * Real.sqrt (1265 : ℝ) := by
    have h4 : (71 : ℝ) ^ 2 ≤ 4 * (1265 : ℝ) := by norm_num
    have h1 := (Real.le_sqrt (by positivity : (0 : ℝ) ≤ (71 : ℝ))
      (by positivity : (0 : ℝ) ≤ 4 * (1265 : ℝ))).mpr h4
    have h2 : Real.sqrt (4 * (1265 : ℝ)) = 2 * Real.sqrt (1265 : ℝ) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 2) (1265 : ℝ),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    rwa [h2] at h1
  have hsT : 71 ≤ 1265 := by norm_num
  have hsub : ((1265 - 71 : ℕ) : ℝ) = (1265 : ℝ) - (71 : ℝ) := by
    rw [Nat.cast_sub hsT]
    norm_num
  have hstep : (1265 : ℝ) - 2 * Real.sqrt (1265 : ℝ) ≤ ((1265 - 71 : ℕ) : ℝ) := by
    rw [hsub]
    linarith [hfloor]
  have hsumI : (1265 - 71) * 10 ^ 4 < ∑ p ∈ plist.filter (· ≤ 1236), clbZ p := by
    rw [hplistLit4]
    decide
  have hsumR : ((1265 - 71 : ℕ) : ℝ) <
      (∑ p ∈ plist.filter (· ≤ 1236), (clbZ p : ℝ)) / 10 ^ 4 := by
    have h1 : ((1265 - 71 : ℕ) : ℝ) * 10 ^ 4
        < ∑ p ∈ plist.filter (· ≤ 1236), (clbZ p : ℝ) := by
      have h2 : ((1265 - 71) * 10 ^ 4 : ℕ) < ∑ p ∈ plist.filter (· ≤ 1236), clbZ p := hsumI
      exact_mod_cast h2
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
    exact h1
  calc (1265 : ℝ) - 2 * Real.sqrt (1265 : ℝ) ≤ ((1265 - 71 : ℕ) : ℝ) := hstep
    _ < (∑ p ∈ plist.filter (· ≤ 1236), (clbZ p : ℝ)) / 10 ^ 4 := hsumR
    _ ≤ ∑ p ∈ plist.filter (· ≤ 1236), Real.log p := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
        calc (∑ p ∈ plist.filter (· ≤ 1236), (clbZ p : ℝ))
            ≤ ∑ p ∈ plist.filter (· ≤ 1236), Real.log p * 10 ^ 4 :=
              Finset.sum_le_sum (fun p hp => theta_cert_clbZ_le_log p (Finset.mem_of_mem_filter p hp))
          _ = (∑ p ∈ plist.filter (· ≤ 1236), Real.log p) * 10 ^ 4 := by rw [Finset.sum_mul]
    _ = Chebyshev.theta ((1236 : ℕ) : ℝ) := by
        rw [Chebyshev.theta_eq_sum_primesLE_log 1236, theta_cert_primesLE_eq 1236 (by norm_num)]

lemma blk_63 : ((1287 : ℕ) : ℝ) - 2 * Real.sqrt ((1287 : ℕ) : ℝ) < Chebyshev.theta ((1265 : ℕ) : ℝ) := by
  have hfloor : (71 : ℝ) ≤ 2 * Real.sqrt (1287 : ℝ) := by
    have h4 : (71 : ℝ) ^ 2 ≤ 4 * (1287 : ℝ) := by norm_num
    have h1 := (Real.le_sqrt (by positivity : (0 : ℝ) ≤ (71 : ℝ))
      (by positivity : (0 : ℝ) ≤ 4 * (1287 : ℝ))).mpr h4
    have h2 : Real.sqrt (4 * (1287 : ℝ)) = 2 * Real.sqrt (1287 : ℝ) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 2) (1287 : ℝ),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    rwa [h2] at h1
  have hsT : 71 ≤ 1287 := by norm_num
  have hsub : ((1287 - 71 : ℕ) : ℝ) = (1287 : ℝ) - (71 : ℝ) := by
    rw [Nat.cast_sub hsT]
    norm_num
  have hstep : (1287 : ℝ) - 2 * Real.sqrt (1287 : ℝ) ≤ ((1287 - 71 : ℕ) : ℝ) := by
    rw [hsub]
    linarith [hfloor]
  have hsumI : (1287 - 71) * 10 ^ 4 < ∑ p ∈ plist.filter (· ≤ 1265), clbZ p := by
    rw [hplistLit4]
    decide
  have hsumR : ((1287 - 71 : ℕ) : ℝ) <
      (∑ p ∈ plist.filter (· ≤ 1265), (clbZ p : ℝ)) / 10 ^ 4 := by
    have h1 : ((1287 - 71 : ℕ) : ℝ) * 10 ^ 4
        < ∑ p ∈ plist.filter (· ≤ 1265), (clbZ p : ℝ) := by
      have h2 : ((1287 - 71) * 10 ^ 4 : ℕ) < ∑ p ∈ plist.filter (· ≤ 1265), clbZ p := hsumI
      exact_mod_cast h2
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
    exact h1
  calc (1287 : ℝ) - 2 * Real.sqrt (1287 : ℝ) ≤ ((1287 - 71 : ℕ) : ℝ) := hstep
    _ < (∑ p ∈ plist.filter (· ≤ 1265), (clbZ p : ℝ)) / 10 ^ 4 := hsumR
    _ ≤ ∑ p ∈ plist.filter (· ≤ 1265), Real.log p := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
        calc (∑ p ∈ plist.filter (· ≤ 1265), (clbZ p : ℝ))
            ≤ ∑ p ∈ plist.filter (· ≤ 1265), Real.log p * 10 ^ 4 :=
              Finset.sum_le_sum (fun p hp => theta_cert_clbZ_le_log p (Finset.mem_of_mem_filter p hp))
          _ = (∑ p ∈ plist.filter (· ≤ 1265), Real.log p) * 10 ^ 4 := by rw [Finset.sum_mul]
    _ = Chebyshev.theta ((1265 : ℕ) : ℝ) := by
        rw [Chebyshev.theta_eq_sum_primesLE_log 1265, theta_cert_primesLE_eq 1265 (by norm_num)]

lemma blk_64 : ((1309 : ℕ) : ℝ) - 2 * Real.sqrt ((1309 : ℕ) : ℝ) < Chebyshev.theta ((1287 : ℕ) : ℝ) := by
  have hfloor : (72 : ℝ) ≤ 2 * Real.sqrt (1309 : ℝ) := by
    have h4 : (72 : ℝ) ^ 2 ≤ 4 * (1309 : ℝ) := by norm_num
    have h1 := (Real.le_sqrt (by positivity : (0 : ℝ) ≤ (72 : ℝ))
      (by positivity : (0 : ℝ) ≤ 4 * (1309 : ℝ))).mpr h4
    have h2 : Real.sqrt (4 * (1309 : ℝ)) = 2 * Real.sqrt (1309 : ℝ) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 2) (1309 : ℝ),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    rwa [h2] at h1
  have hsT : 72 ≤ 1309 := by norm_num
  have hsub : ((1309 - 72 : ℕ) : ℝ) = (1309 : ℝ) - (72 : ℝ) := by
    rw [Nat.cast_sub hsT]
    norm_num
  have hstep : (1309 : ℝ) - 2 * Real.sqrt (1309 : ℝ) ≤ ((1309 - 72 : ℕ) : ℝ) := by
    rw [hsub]
    linarith [hfloor]
  have hsumI : (1309 - 72) * 10 ^ 4 < ∑ p ∈ plist.filter (· ≤ 1287), clbZ p := by
    rw [hplistLit4]
    decide
  have hsumR : ((1309 - 72 : ℕ) : ℝ) <
      (∑ p ∈ plist.filter (· ≤ 1287), (clbZ p : ℝ)) / 10 ^ 4 := by
    have h1 : ((1309 - 72 : ℕ) : ℝ) * 10 ^ 4
        < ∑ p ∈ plist.filter (· ≤ 1287), (clbZ p : ℝ) := by
      have h2 : ((1309 - 72) * 10 ^ 4 : ℕ) < ∑ p ∈ plist.filter (· ≤ 1287), clbZ p := hsumI
      exact_mod_cast h2
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
    exact h1
  calc (1309 : ℝ) - 2 * Real.sqrt (1309 : ℝ) ≤ ((1309 - 72 : ℕ) : ℝ) := hstep
    _ < (∑ p ∈ plist.filter (· ≤ 1287), (clbZ p : ℝ)) / 10 ^ 4 := hsumR
    _ ≤ ∑ p ∈ plist.filter (· ≤ 1287), Real.log p := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
        calc (∑ p ∈ plist.filter (· ≤ 1287), (clbZ p : ℝ))
            ≤ ∑ p ∈ plist.filter (· ≤ 1287), Real.log p * 10 ^ 4 :=
              Finset.sum_le_sum (fun p hp => theta_cert_clbZ_le_log p (Finset.mem_of_mem_filter p hp))
          _ = (∑ p ∈ plist.filter (· ≤ 1287), Real.log p) * 10 ^ 4 := by rw [Finset.sum_mul]
    _ = Chebyshev.theta ((1287 : ℕ) : ℝ) := by
        rw [Chebyshev.theta_eq_sum_primesLE_log 1287, theta_cert_primesLE_eq 1287 (by norm_num)]

lemma blk_65 : ((1353 : ℕ) : ℝ) - 2 * Real.sqrt ((1353 : ℕ) : ℝ) < Chebyshev.theta ((1309 : ℕ) : ℝ) := by
  have hfloor : (73 : ℝ) ≤ 2 * Real.sqrt (1353 : ℝ) := by
    have h4 : (73 : ℝ) ^ 2 ≤ 4 * (1353 : ℝ) := by norm_num
    have h1 := (Real.le_sqrt (by positivity : (0 : ℝ) ≤ (73 : ℝ))
      (by positivity : (0 : ℝ) ≤ 4 * (1353 : ℝ))).mpr h4
    have h2 : Real.sqrt (4 * (1353 : ℝ)) = 2 * Real.sqrt (1353 : ℝ) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 2) (1353 : ℝ),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    rwa [h2] at h1
  have hsT : 73 ≤ 1353 := by norm_num
  have hsub : ((1353 - 73 : ℕ) : ℝ) = (1353 : ℝ) - (73 : ℝ) := by
    rw [Nat.cast_sub hsT]
    norm_num
  have hstep : (1353 : ℝ) - 2 * Real.sqrt (1353 : ℝ) ≤ ((1353 - 73 : ℕ) : ℝ) := by
    rw [hsub]
    linarith [hfloor]
  have hsumI : (1353 - 73) * 10 ^ 4 < ∑ p ∈ plist.filter (· ≤ 1309), clbZ p := by
    rw [hplistLit4]
    decide
  have hsumR : ((1353 - 73 : ℕ) : ℝ) <
      (∑ p ∈ plist.filter (· ≤ 1309), (clbZ p : ℝ)) / 10 ^ 4 := by
    have h1 : ((1353 - 73 : ℕ) : ℝ) * 10 ^ 4
        < ∑ p ∈ plist.filter (· ≤ 1309), (clbZ p : ℝ) := by
      have h2 : ((1353 - 73) * 10 ^ 4 : ℕ) < ∑ p ∈ plist.filter (· ≤ 1309), clbZ p := hsumI
      exact_mod_cast h2
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
    exact h1
  calc (1353 : ℝ) - 2 * Real.sqrt (1353 : ℝ) ≤ ((1353 - 73 : ℕ) : ℝ) := hstep
    _ < (∑ p ∈ plist.filter (· ≤ 1309), (clbZ p : ℝ)) / 10 ^ 4 := hsumR
    _ ≤ ∑ p ∈ plist.filter (· ≤ 1309), Real.log p := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
        calc (∑ p ∈ plist.filter (· ≤ 1309), (clbZ p : ℝ))
            ≤ ∑ p ∈ plist.filter (· ≤ 1309), Real.log p * 10 ^ 4 :=
              Finset.sum_le_sum (fun p hp => theta_cert_clbZ_le_log p (Finset.mem_of_mem_filter p hp))
          _ = (∑ p ∈ plist.filter (· ≤ 1309), Real.log p) * 10 ^ 4 := by rw [Finset.sum_mul]
    _ = Chebyshev.theta ((1309 : ℕ) : ℝ) := by
        rw [Chebyshev.theta_eq_sum_primesLE_log 1309, theta_cert_primesLE_eq 1309 (by norm_num)]

lemma blk_66 : ((1376 : ℕ) : ℝ) - 2 * Real.sqrt ((1376 : ℕ) : ℝ) < Chebyshev.theta ((1353 : ℕ) : ℝ) := by
  have hfloor : (74 : ℝ) ≤ 2 * Real.sqrt (1376 : ℝ) := by
    have h4 : (74 : ℝ) ^ 2 ≤ 4 * (1376 : ℝ) := by norm_num
    have h1 := (Real.le_sqrt (by positivity : (0 : ℝ) ≤ (74 : ℝ))
      (by positivity : (0 : ℝ) ≤ 4 * (1376 : ℝ))).mpr h4
    have h2 : Real.sqrt (4 * (1376 : ℝ)) = 2 * Real.sqrt (1376 : ℝ) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 2) (1376 : ℝ),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    rwa [h2] at h1
  have hsT : 74 ≤ 1376 := by norm_num
  have hsub : ((1376 - 74 : ℕ) : ℝ) = (1376 : ℝ) - (74 : ℝ) := by
    rw [Nat.cast_sub hsT]
    norm_num
  have hstep : (1376 : ℝ) - 2 * Real.sqrt (1376 : ℝ) ≤ ((1376 - 74 : ℕ) : ℝ) := by
    rw [hsub]
    linarith [hfloor]
  have hsumI : (1376 - 74) * 10 ^ 4 < ∑ p ∈ plist.filter (· ≤ 1353), clbZ p := by
    rw [hplistLit4]
    decide
  have hsumR : ((1376 - 74 : ℕ) : ℝ) <
      (∑ p ∈ plist.filter (· ≤ 1353), (clbZ p : ℝ)) / 10 ^ 4 := by
    have h1 : ((1376 - 74 : ℕ) : ℝ) * 10 ^ 4
        < ∑ p ∈ plist.filter (· ≤ 1353), (clbZ p : ℝ) := by
      have h2 : ((1376 - 74) * 10 ^ 4 : ℕ) < ∑ p ∈ plist.filter (· ≤ 1353), clbZ p := hsumI
      exact_mod_cast h2
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
    exact h1
  calc (1376 : ℝ) - 2 * Real.sqrt (1376 : ℝ) ≤ ((1376 - 74 : ℕ) : ℝ) := hstep
    _ < (∑ p ∈ plist.filter (· ≤ 1353), (clbZ p : ℝ)) / 10 ^ 4 := hsumR
    _ ≤ ∑ p ∈ plist.filter (· ≤ 1353), Real.log p := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
        calc (∑ p ∈ plist.filter (· ≤ 1353), (clbZ p : ℝ))
            ≤ ∑ p ∈ plist.filter (· ≤ 1353), Real.log p * 10 ^ 4 :=
              Finset.sum_le_sum (fun p hp => theta_cert_clbZ_le_log p (Finset.mem_of_mem_filter p hp))
          _ = (∑ p ∈ plist.filter (· ≤ 1353), Real.log p) * 10 ^ 4 := by rw [Finset.sum_mul]
    _ = Chebyshev.theta ((1353 : ℕ) : ℝ) := by
        rw [Chebyshev.theta_eq_sum_primesLE_log 1353, theta_cert_primesLE_eq 1353 (by norm_num)]

lemma blk_67 : ((1397 : ℕ) : ℝ) - 2 * Real.sqrt ((1397 : ℕ) : ℝ) < Chebyshev.theta ((1376 : ℕ) : ℝ) := by
  have hfloor : (74 : ℝ) ≤ 2 * Real.sqrt (1397 : ℝ) := by
    have h4 : (74 : ℝ) ^ 2 ≤ 4 * (1397 : ℝ) := by norm_num
    have h1 := (Real.le_sqrt (by positivity : (0 : ℝ) ≤ (74 : ℝ))
      (by positivity : (0 : ℝ) ≤ 4 * (1397 : ℝ))).mpr h4
    have h2 : Real.sqrt (4 * (1397 : ℝ)) = 2 * Real.sqrt (1397 : ℝ) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 2) (1397 : ℝ),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    rwa [h2] at h1
  have hsT : 74 ≤ 1397 := by norm_num
  have hsub : ((1397 - 74 : ℕ) : ℝ) = (1397 : ℝ) - (74 : ℝ) := by
    rw [Nat.cast_sub hsT]
    norm_num
  have hstep : (1397 : ℝ) - 2 * Real.sqrt (1397 : ℝ) ≤ ((1397 - 74 : ℕ) : ℝ) := by
    rw [hsub]
    linarith [hfloor]
  have hsumI : (1397 - 74) * 10 ^ 4 < ∑ p ∈ plist.filter (· ≤ 1376), clbZ p := by
    rw [hplistLit4]
    decide
  have hsumR : ((1397 - 74 : ℕ) : ℝ) <
      (∑ p ∈ plist.filter (· ≤ 1376), (clbZ p : ℝ)) / 10 ^ 4 := by
    have h1 : ((1397 - 74 : ℕ) : ℝ) * 10 ^ 4
        < ∑ p ∈ plist.filter (· ≤ 1376), (clbZ p : ℝ) := by
      have h2 : ((1397 - 74) * 10 ^ 4 : ℕ) < ∑ p ∈ plist.filter (· ≤ 1376), clbZ p := hsumI
      exact_mod_cast h2
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
    exact h1
  calc (1397 : ℝ) - 2 * Real.sqrt (1397 : ℝ) ≤ ((1397 - 74 : ℕ) : ℝ) := hstep
    _ < (∑ p ∈ plist.filter (· ≤ 1376), (clbZ p : ℝ)) / 10 ^ 4 := hsumR
    _ ≤ ∑ p ∈ plist.filter (· ≤ 1376), Real.log p := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
        calc (∑ p ∈ plist.filter (· ≤ 1376), (clbZ p : ℝ))
            ≤ ∑ p ∈ plist.filter (· ≤ 1376), Real.log p * 10 ^ 4 :=
              Finset.sum_le_sum (fun p hp => theta_cert_clbZ_le_log p (Finset.mem_of_mem_filter p hp))
          _ = (∑ p ∈ plist.filter (· ≤ 1376), Real.log p) * 10 ^ 4 := by rw [Finset.sum_mul]
    _ = Chebyshev.theta ((1376 : ℕ) : ℝ) := by
        rw [Chebyshev.theta_eq_sum_primesLE_log 1376, theta_cert_primesLE_eq 1376 (by norm_num)]

lemma blk_68 : ((1405 : ℕ) : ℝ) - 2 * Real.sqrt ((1405 : ℕ) : ℝ) < Chebyshev.theta ((1397 : ℕ) : ℝ) := by
  have hfloor : (74 : ℝ) ≤ 2 * Real.sqrt (1405 : ℝ) := by
    have h4 : (74 : ℝ) ^ 2 ≤ 4 * (1405 : ℝ) := by norm_num
    have h1 := (Real.le_sqrt (by positivity : (0 : ℝ) ≤ (74 : ℝ))
      (by positivity : (0 : ℝ) ≤ 4 * (1405 : ℝ))).mpr h4
    have h2 : Real.sqrt (4 * (1405 : ℝ)) = 2 * Real.sqrt (1405 : ℝ) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 2) (1405 : ℝ),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    rwa [h2] at h1
  have hsT : 74 ≤ 1405 := by norm_num
  have hsub : ((1405 - 74 : ℕ) : ℝ) = (1405 : ℝ) - (74 : ℝ) := by
    rw [Nat.cast_sub hsT]
    norm_num
  have hstep : (1405 : ℝ) - 2 * Real.sqrt (1405 : ℝ) ≤ ((1405 - 74 : ℕ) : ℝ) := by
    rw [hsub]
    linarith [hfloor]
  have hsumI : (1405 - 74) * 10 ^ 4 < ∑ p ∈ plist.filter (· ≤ 1397), clbZ p := by
    rw [hplistLit4]
    decide
  have hsumR : ((1405 - 74 : ℕ) : ℝ) <
      (∑ p ∈ plist.filter (· ≤ 1397), (clbZ p : ℝ)) / 10 ^ 4 := by
    have h1 : ((1405 - 74 : ℕ) : ℝ) * 10 ^ 4
        < ∑ p ∈ plist.filter (· ≤ 1397), (clbZ p : ℝ) := by
      have h2 : ((1405 - 74) * 10 ^ 4 : ℕ) < ∑ p ∈ plist.filter (· ≤ 1397), clbZ p := hsumI
      exact_mod_cast h2
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
    exact h1
  calc (1405 : ℝ) - 2 * Real.sqrt (1405 : ℝ) ≤ ((1405 - 74 : ℕ) : ℝ) := hstep
    _ < (∑ p ∈ plist.filter (· ≤ 1397), (clbZ p : ℝ)) / 10 ^ 4 := hsumR
    _ ≤ ∑ p ∈ plist.filter (· ≤ 1397), Real.log p := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
        calc (∑ p ∈ plist.filter (· ≤ 1397), (clbZ p : ℝ))
            ≤ ∑ p ∈ plist.filter (· ≤ 1397), Real.log p * 10 ^ 4 :=
              Finset.sum_le_sum (fun p hp => theta_cert_clbZ_le_log p (Finset.mem_of_mem_filter p hp))
          _ = (∑ p ∈ plist.filter (· ≤ 1397), Real.log p) * 10 ^ 4 := by rw [Finset.sum_mul]
    _ = Chebyshev.theta ((1397 : ℕ) : ℝ) := by
        rw [Chebyshev.theta_eq_sum_primesLE_log 1397, theta_cert_primesLE_eq 1397 (by norm_num)]

lemma blk_69 : ((1413 : ℕ) : ℝ) - 2 * Real.sqrt ((1413 : ℕ) : ℝ) < Chebyshev.theta ((1405 : ℕ) : ℝ) := by
  have hfloor : (75 : ℝ) ≤ 2 * Real.sqrt (1413 : ℝ) := by
    have h4 : (75 : ℝ) ^ 2 ≤ 4 * (1413 : ℝ) := by norm_num
    have h1 := (Real.le_sqrt (by positivity : (0 : ℝ) ≤ (75 : ℝ))
      (by positivity : (0 : ℝ) ≤ 4 * (1413 : ℝ))).mpr h4
    have h2 : Real.sqrt (4 * (1413 : ℝ)) = 2 * Real.sqrt (1413 : ℝ) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 2) (1413 : ℝ),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    rwa [h2] at h1
  have hsT : 75 ≤ 1413 := by norm_num
  have hsub : ((1413 - 75 : ℕ) : ℝ) = (1413 : ℝ) - (75 : ℝ) := by
    rw [Nat.cast_sub hsT]
    norm_num
  have hstep : (1413 : ℝ) - 2 * Real.sqrt (1413 : ℝ) ≤ ((1413 - 75 : ℕ) : ℝ) := by
    rw [hsub]
    linarith [hfloor]
  have hsumI : (1413 - 75) * 10 ^ 4 < ∑ p ∈ plist.filter (· ≤ 1405), clbZ p := by
    rw [hplistLit4]
    decide
  have hsumR : ((1413 - 75 : ℕ) : ℝ) <
      (∑ p ∈ plist.filter (· ≤ 1405), (clbZ p : ℝ)) / 10 ^ 4 := by
    have h1 : ((1413 - 75 : ℕ) : ℝ) * 10 ^ 4
        < ∑ p ∈ plist.filter (· ≤ 1405), (clbZ p : ℝ) := by
      have h2 : ((1413 - 75) * 10 ^ 4 : ℕ) < ∑ p ∈ plist.filter (· ≤ 1405), clbZ p := hsumI
      exact_mod_cast h2
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
    exact h1
  calc (1413 : ℝ) - 2 * Real.sqrt (1413 : ℝ) ≤ ((1413 - 75 : ℕ) : ℝ) := hstep
    _ < (∑ p ∈ plist.filter (· ≤ 1405), (clbZ p : ℝ)) / 10 ^ 4 := hsumR
    _ ≤ ∑ p ∈ plist.filter (· ≤ 1405), Real.log p := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
        calc (∑ p ∈ plist.filter (· ≤ 1405), (clbZ p : ℝ))
            ≤ ∑ p ∈ plist.filter (· ≤ 1405), Real.log p * 10 ^ 4 :=
              Finset.sum_le_sum (fun p hp => theta_cert_clbZ_le_log p (Finset.mem_of_mem_filter p hp))
          _ = (∑ p ∈ plist.filter (· ≤ 1405), Real.log p) * 10 ^ 4 := by rw [Finset.sum_mul]
    _ = Chebyshev.theta ((1405 : ℕ) : ℝ) := by
        rw [Chebyshev.theta_eq_sum_primesLE_log 1405, theta_cert_primesLE_eq 1405 (by norm_num)]

lemma blk_70 : ((1420 : ℕ) : ℝ) - 2 * Real.sqrt ((1420 : ℕ) : ℝ) < Chebyshev.theta ((1413 : ℕ) : ℝ) := by
  have hfloor : (75 : ℝ) ≤ 2 * Real.sqrt (1420 : ℝ) := by
    have h4 : (75 : ℝ) ^ 2 ≤ 4 * (1420 : ℝ) := by norm_num
    have h1 := (Real.le_sqrt (by positivity : (0 : ℝ) ≤ (75 : ℝ))
      (by positivity : (0 : ℝ) ≤ 4 * (1420 : ℝ))).mpr h4
    have h2 : Real.sqrt (4 * (1420 : ℝ)) = 2 * Real.sqrt (1420 : ℝ) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 2) (1420 : ℝ),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    rwa [h2] at h1
  have hsT : 75 ≤ 1420 := by norm_num
  have hsub : ((1420 - 75 : ℕ) : ℝ) = (1420 : ℝ) - (75 : ℝ) := by
    rw [Nat.cast_sub hsT]
    norm_num
  have hstep : (1420 : ℝ) - 2 * Real.sqrt (1420 : ℝ) ≤ ((1420 - 75 : ℕ) : ℝ) := by
    rw [hsub]
    linarith [hfloor]
  have hsumI : (1420 - 75) * 10 ^ 4 < ∑ p ∈ plist.filter (· ≤ 1413), clbZ p := by
    rw [hplistLit4]
    decide
  have hsumR : ((1420 - 75 : ℕ) : ℝ) <
      (∑ p ∈ plist.filter (· ≤ 1413), (clbZ p : ℝ)) / 10 ^ 4 := by
    have h1 : ((1420 - 75 : ℕ) : ℝ) * 10 ^ 4
        < ∑ p ∈ plist.filter (· ≤ 1413), (clbZ p : ℝ) := by
      have h2 : ((1420 - 75) * 10 ^ 4 : ℕ) < ∑ p ∈ plist.filter (· ≤ 1413), clbZ p := hsumI
      exact_mod_cast h2
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
    exact h1
  calc (1420 : ℝ) - 2 * Real.sqrt (1420 : ℝ) ≤ ((1420 - 75 : ℕ) : ℝ) := hstep
    _ < (∑ p ∈ plist.filter (· ≤ 1413), (clbZ p : ℝ)) / 10 ^ 4 := hsumR
    _ ≤ ∑ p ∈ plist.filter (· ≤ 1413), Real.log p := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
        calc (∑ p ∈ plist.filter (· ≤ 1413), (clbZ p : ℝ))
            ≤ ∑ p ∈ plist.filter (· ≤ 1413), Real.log p * 10 ^ 4 :=
              Finset.sum_le_sum (fun p hp => theta_cert_clbZ_le_log p (Finset.mem_of_mem_filter p hp))
          _ = (∑ p ∈ plist.filter (· ≤ 1413), Real.log p) * 10 ^ 4 := by rw [Finset.sum_mul]
    _ = Chebyshev.theta ((1413 : ℕ) : ℝ) := by
        rw [Chebyshev.theta_eq_sum_primesLE_log 1413, theta_cert_primesLE_eq 1413 (by norm_num)]


theorem solution (ab : ℕ × ℕ) (hab : ab ∈ blk4) :
    ((min (ab.2 + 1) 1420 : ℕ) : ℝ) - 2 * Real.sqrt ((min (ab.2 + 1) 1420 : ℕ) : ℝ) <
      Chebyshev.theta ((ab.1 : ℕ) : ℝ) := by
  have hmem := hab
  simp only [blk4, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals cases h
  all_goals (first | exact blk_53 | exact blk_54 | exact blk_55 | exact blk_56 | exact blk_57 | exact blk_58 | exact blk_59 | exact blk_60 | exact blk_61 | exact blk_62 | exact blk_63 | exact blk_64 | exact blk_65 | exact blk_66 | exact blk_67 | exact blk_68 | exact blk_69 | exact blk_70)

end TaoFivePrimes


open TaoFivePrimes

/-- The verification harness looks for `theorem solution` in the root
namespace, so the namespaced proof above is re-exported at the root. -/
theorem solution (ab : ℕ × ℕ) (hab : ab ∈ blk4) :
    ((min (ab.2 + 1) 1420 : ℕ) : ℝ) - 2 * Real.sqrt ((min (ab.2 + 1) 1420 : ℕ) : ℝ) <
      Chebyshev.theta ((ab.1 : ℕ) : ℝ) :=
  TaoFivePrimes.solution ab hab
