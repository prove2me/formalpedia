-- Prove2me | solution 1 for TaoFivePrimes.theta_cert_blocks_3
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T14:23:06.82853+00:00
-- url     : https://prove2.me/submissions/d77143ae-5b31-4789-9ddc-399b8163cf03

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

def plistLit3 : Finset ℕ :=
  ⟨(↑([2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021, 1031, 1033, 1039, 1049, 1051, 1061, 1063, 1069, 1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163, 1171, 1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249, 1259, 1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367, 1373, 1381, 1399, 1409] : List ℕ) : Multiset ℕ), by decide⟩

lemma hplistLit3 : plist = plistLit3 := by decide

lemma blk_35 : ((671 : ℕ) : ℝ) - 2 * Real.sqrt ((671 : ℕ) : ℝ) < Chebyshev.theta ((652 : ℕ) : ℝ) := by
  have hfloor : (51 : ℝ) ≤ 2 * Real.sqrt (671 : ℝ) := by
    have h4 : (51 : ℝ) ^ 2 ≤ 4 * (671 : ℝ) := by norm_num
    have h1 := (Real.le_sqrt (by positivity : (0 : ℝ) ≤ (51 : ℝ))
      (by positivity : (0 : ℝ) ≤ 4 * (671 : ℝ))).mpr h4
    have h2 : Real.sqrt (4 * (671 : ℝ)) = 2 * Real.sqrt (671 : ℝ) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 2) (671 : ℝ),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    rwa [h2] at h1
  have hsT : 51 ≤ 671 := by norm_num
  have hsub : ((671 - 51 : ℕ) : ℝ) = (671 : ℝ) - (51 : ℝ) := by
    rw [Nat.cast_sub hsT]
    norm_num
  have hstep : (671 : ℝ) - 2 * Real.sqrt (671 : ℝ) ≤ ((671 - 51 : ℕ) : ℝ) := by
    rw [hsub]
    linarith [hfloor]
  have hsumI : (671 - 51) * 10 ^ 4 < ∑ p ∈ plist.filter (· ≤ 652), clbZ p := by
    rw [hplistLit3]
    decide
  have hsumR : ((671 - 51 : ℕ) : ℝ) <
      (∑ p ∈ plist.filter (· ≤ 652), (clbZ p : ℝ)) / 10 ^ 4 := by
    have h1 : ((671 - 51 : ℕ) : ℝ) * 10 ^ 4
        < ∑ p ∈ plist.filter (· ≤ 652), (clbZ p : ℝ) := by
      have h2 : ((671 - 51) * 10 ^ 4 : ℕ) < ∑ p ∈ plist.filter (· ≤ 652), clbZ p := hsumI
      exact_mod_cast h2
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
    exact h1
  calc (671 : ℝ) - 2 * Real.sqrt (671 : ℝ) ≤ ((671 - 51 : ℕ) : ℝ) := hstep
    _ < (∑ p ∈ plist.filter (· ≤ 652), (clbZ p : ℝ)) / 10 ^ 4 := hsumR
    _ ≤ ∑ p ∈ plist.filter (· ≤ 652), Real.log p := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
        calc (∑ p ∈ plist.filter (· ≤ 652), (clbZ p : ℝ))
            ≤ ∑ p ∈ plist.filter (· ≤ 652), Real.log p * 10 ^ 4 :=
              Finset.sum_le_sum (fun p hp => theta_cert_clbZ_le_log p (Finset.mem_of_mem_filter p hp))
          _ = (∑ p ∈ plist.filter (· ≤ 652), Real.log p) * 10 ^ 4 := by rw [Finset.sum_mul]
    _ = Chebyshev.theta ((652 : ℕ) : ℝ) := by
        rw [Chebyshev.theta_eq_sum_primesLE_log 652, theta_cert_primesLE_eq 652 (by norm_num)]

lemma blk_36 : ((692 : ℕ) : ℝ) - 2 * Real.sqrt ((692 : ℕ) : ℝ) < Chebyshev.theta ((671 : ℕ) : ℝ) := by
  have hfloor : (52 : ℝ) ≤ 2 * Real.sqrt (692 : ℝ) := by
    have h4 : (52 : ℝ) ^ 2 ≤ 4 * (692 : ℝ) := by norm_num
    have h1 := (Real.le_sqrt (by positivity : (0 : ℝ) ≤ (52 : ℝ))
      (by positivity : (0 : ℝ) ≤ 4 * (692 : ℝ))).mpr h4
    have h2 : Real.sqrt (4 * (692 : ℝ)) = 2 * Real.sqrt (692 : ℝ) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 2) (692 : ℝ),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    rwa [h2] at h1
  have hsT : 52 ≤ 692 := by norm_num
  have hsub : ((692 - 52 : ℕ) : ℝ) = (692 : ℝ) - (52 : ℝ) := by
    rw [Nat.cast_sub hsT]
    norm_num
  have hstep : (692 : ℝ) - 2 * Real.sqrt (692 : ℝ) ≤ ((692 - 52 : ℕ) : ℝ) := by
    rw [hsub]
    linarith [hfloor]
  have hsumI : (692 - 52) * 10 ^ 4 < ∑ p ∈ plist.filter (· ≤ 671), clbZ p := by
    rw [hplistLit3]
    decide
  have hsumR : ((692 - 52 : ℕ) : ℝ) <
      (∑ p ∈ plist.filter (· ≤ 671), (clbZ p : ℝ)) / 10 ^ 4 := by
    have h1 : ((692 - 52 : ℕ) : ℝ) * 10 ^ 4
        < ∑ p ∈ plist.filter (· ≤ 671), (clbZ p : ℝ) := by
      have h2 : ((692 - 52) * 10 ^ 4 : ℕ) < ∑ p ∈ plist.filter (· ≤ 671), clbZ p := hsumI
      exact_mod_cast h2
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
    exact h1
  calc (692 : ℝ) - 2 * Real.sqrt (692 : ℝ) ≤ ((692 - 52 : ℕ) : ℝ) := hstep
    _ < (∑ p ∈ plist.filter (· ≤ 671), (clbZ p : ℝ)) / 10 ^ 4 := hsumR
    _ ≤ ∑ p ∈ plist.filter (· ≤ 671), Real.log p := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
        calc (∑ p ∈ plist.filter (· ≤ 671), (clbZ p : ℝ))
            ≤ ∑ p ∈ plist.filter (· ≤ 671), Real.log p * 10 ^ 4 :=
              Finset.sum_le_sum (fun p hp => theta_cert_clbZ_le_log p (Finset.mem_of_mem_filter p hp))
          _ = (∑ p ∈ plist.filter (· ≤ 671), Real.log p) * 10 ^ 4 := by rw [Finset.sum_mul]
    _ = Chebyshev.theta ((671 : ℕ) : ℝ) := by
        rw [Chebyshev.theta_eq_sum_primesLE_log 671, theta_cert_primesLE_eq 671 (by norm_num)]

lemma blk_37 : ((719 : ℕ) : ℝ) - 2 * Real.sqrt ((719 : ℕ) : ℝ) < Chebyshev.theta ((692 : ℕ) : ℝ) := by
  have hfloor : (53 : ℝ) ≤ 2 * Real.sqrt (719 : ℝ) := by
    have h4 : (53 : ℝ) ^ 2 ≤ 4 * (719 : ℝ) := by norm_num
    have h1 := (Real.le_sqrt (by positivity : (0 : ℝ) ≤ (53 : ℝ))
      (by positivity : (0 : ℝ) ≤ 4 * (719 : ℝ))).mpr h4
    have h2 : Real.sqrt (4 * (719 : ℝ)) = 2 * Real.sqrt (719 : ℝ) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 2) (719 : ℝ),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    rwa [h2] at h1
  have hsT : 53 ≤ 719 := by norm_num
  have hsub : ((719 - 53 : ℕ) : ℝ) = (719 : ℝ) - (53 : ℝ) := by
    rw [Nat.cast_sub hsT]
    norm_num
  have hstep : (719 : ℝ) - 2 * Real.sqrt (719 : ℝ) ≤ ((719 - 53 : ℕ) : ℝ) := by
    rw [hsub]
    linarith [hfloor]
  have hsumI : (719 - 53) * 10 ^ 4 < ∑ p ∈ plist.filter (· ≤ 692), clbZ p := by
    rw [hplistLit3]
    decide
  have hsumR : ((719 - 53 : ℕ) : ℝ) <
      (∑ p ∈ plist.filter (· ≤ 692), (clbZ p : ℝ)) / 10 ^ 4 := by
    have h1 : ((719 - 53 : ℕ) : ℝ) * 10 ^ 4
        < ∑ p ∈ plist.filter (· ≤ 692), (clbZ p : ℝ) := by
      have h2 : ((719 - 53) * 10 ^ 4 : ℕ) < ∑ p ∈ plist.filter (· ≤ 692), clbZ p := hsumI
      exact_mod_cast h2
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
    exact h1
  calc (719 : ℝ) - 2 * Real.sqrt (719 : ℝ) ≤ ((719 - 53 : ℕ) : ℝ) := hstep
    _ < (∑ p ∈ plist.filter (· ≤ 692), (clbZ p : ℝ)) / 10 ^ 4 := hsumR
    _ ≤ ∑ p ∈ plist.filter (· ≤ 692), Real.log p := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
        calc (∑ p ∈ plist.filter (· ≤ 692), (clbZ p : ℝ))
            ≤ ∑ p ∈ plist.filter (· ≤ 692), Real.log p * 10 ^ 4 :=
              Finset.sum_le_sum (fun p hp => theta_cert_clbZ_le_log p (Finset.mem_of_mem_filter p hp))
          _ = (∑ p ∈ plist.filter (· ≤ 692), Real.log p) * 10 ^ 4 := by rw [Finset.sum_mul]
    _ = Chebyshev.theta ((692 : ℕ) : ℝ) := by
        rw [Chebyshev.theta_eq_sum_primesLE_log 692, theta_cert_primesLE_eq 692 (by norm_num)]

lemma blk_38 : ((740 : ℕ) : ℝ) - 2 * Real.sqrt ((740 : ℕ) : ℝ) < Chebyshev.theta ((719 : ℕ) : ℝ) := by
  have hfloor : (54 : ℝ) ≤ 2 * Real.sqrt (740 : ℝ) := by
    have h4 : (54 : ℝ) ^ 2 ≤ 4 * (740 : ℝ) := by norm_num
    have h1 := (Real.le_sqrt (by positivity : (0 : ℝ) ≤ (54 : ℝ))
      (by positivity : (0 : ℝ) ≤ 4 * (740 : ℝ))).mpr h4
    have h2 : Real.sqrt (4 * (740 : ℝ)) = 2 * Real.sqrt (740 : ℝ) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 2) (740 : ℝ),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    rwa [h2] at h1
  have hsT : 54 ≤ 740 := by norm_num
  have hsub : ((740 - 54 : ℕ) : ℝ) = (740 : ℝ) - (54 : ℝ) := by
    rw [Nat.cast_sub hsT]
    norm_num
  have hstep : (740 : ℝ) - 2 * Real.sqrt (740 : ℝ) ≤ ((740 - 54 : ℕ) : ℝ) := by
    rw [hsub]
    linarith [hfloor]
  have hsumI : (740 - 54) * 10 ^ 4 < ∑ p ∈ plist.filter (· ≤ 719), clbZ p := by
    rw [hplistLit3]
    decide
  have hsumR : ((740 - 54 : ℕ) : ℝ) <
      (∑ p ∈ plist.filter (· ≤ 719), (clbZ p : ℝ)) / 10 ^ 4 := by
    have h1 : ((740 - 54 : ℕ) : ℝ) * 10 ^ 4
        < ∑ p ∈ plist.filter (· ≤ 719), (clbZ p : ℝ) := by
      have h2 : ((740 - 54) * 10 ^ 4 : ℕ) < ∑ p ∈ plist.filter (· ≤ 719), clbZ p := hsumI
      exact_mod_cast h2
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
    exact h1
  calc (740 : ℝ) - 2 * Real.sqrt (740 : ℝ) ≤ ((740 - 54 : ℕ) : ℝ) := hstep
    _ < (∑ p ∈ plist.filter (· ≤ 719), (clbZ p : ℝ)) / 10 ^ 4 := hsumR
    _ ≤ ∑ p ∈ plist.filter (· ≤ 719), Real.log p := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
        calc (∑ p ∈ plist.filter (· ≤ 719), (clbZ p : ℝ))
            ≤ ∑ p ∈ plist.filter (· ≤ 719), Real.log p * 10 ^ 4 :=
              Finset.sum_le_sum (fun p hp => theta_cert_clbZ_le_log p (Finset.mem_of_mem_filter p hp))
          _ = (∑ p ∈ plist.filter (· ≤ 719), Real.log p) * 10 ^ 4 := by rw [Finset.sum_mul]
    _ = Chebyshev.theta ((719 : ℕ) : ℝ) := by
        rw [Chebyshev.theta_eq_sum_primesLE_log 719, theta_cert_primesLE_eq 719 (by norm_num)]

lemma blk_39 : ((760 : ℕ) : ℝ) - 2 * Real.sqrt ((760 : ℕ) : ℝ) < Chebyshev.theta ((740 : ℕ) : ℝ) := by
  have hfloor : (55 : ℝ) ≤ 2 * Real.sqrt (760 : ℝ) := by
    have h4 : (55 : ℝ) ^ 2 ≤ 4 * (760 : ℝ) := by norm_num
    have h1 := (Real.le_sqrt (by positivity : (0 : ℝ) ≤ (55 : ℝ))
      (by positivity : (0 : ℝ) ≤ 4 * (760 : ℝ))).mpr h4
    have h2 : Real.sqrt (4 * (760 : ℝ)) = 2 * Real.sqrt (760 : ℝ) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 2) (760 : ℝ),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    rwa [h2] at h1
  have hsT : 55 ≤ 760 := by norm_num
  have hsub : ((760 - 55 : ℕ) : ℝ) = (760 : ℝ) - (55 : ℝ) := by
    rw [Nat.cast_sub hsT]
    norm_num
  have hstep : (760 : ℝ) - 2 * Real.sqrt (760 : ℝ) ≤ ((760 - 55 : ℕ) : ℝ) := by
    rw [hsub]
    linarith [hfloor]
  have hsumI : (760 - 55) * 10 ^ 4 < ∑ p ∈ plist.filter (· ≤ 740), clbZ p := by
    rw [hplistLit3]
    decide
  have hsumR : ((760 - 55 : ℕ) : ℝ) <
      (∑ p ∈ plist.filter (· ≤ 740), (clbZ p : ℝ)) / 10 ^ 4 := by
    have h1 : ((760 - 55 : ℕ) : ℝ) * 10 ^ 4
        < ∑ p ∈ plist.filter (· ≤ 740), (clbZ p : ℝ) := by
      have h2 : ((760 - 55) * 10 ^ 4 : ℕ) < ∑ p ∈ plist.filter (· ≤ 740), clbZ p := hsumI
      exact_mod_cast h2
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
    exact h1
  calc (760 : ℝ) - 2 * Real.sqrt (760 : ℝ) ≤ ((760 - 55 : ℕ) : ℝ) := hstep
    _ < (∑ p ∈ plist.filter (· ≤ 740), (clbZ p : ℝ)) / 10 ^ 4 := hsumR
    _ ≤ ∑ p ∈ plist.filter (· ≤ 740), Real.log p := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
        calc (∑ p ∈ plist.filter (· ≤ 740), (clbZ p : ℝ))
            ≤ ∑ p ∈ plist.filter (· ≤ 740), Real.log p * 10 ^ 4 :=
              Finset.sum_le_sum (fun p hp => theta_cert_clbZ_le_log p (Finset.mem_of_mem_filter p hp))
          _ = (∑ p ∈ plist.filter (· ≤ 740), Real.log p) * 10 ^ 4 := by rw [Finset.sum_mul]
    _ = Chebyshev.theta ((740 : ℕ) : ℝ) := by
        rw [Chebyshev.theta_eq_sum_primesLE_log 740, theta_cert_primesLE_eq 740 (by norm_num)]

lemma blk_40 : ((780 : ℕ) : ℝ) - 2 * Real.sqrt ((780 : ℕ) : ℝ) < Chebyshev.theta ((760 : ℕ) : ℝ) := by
  have hfloor : (55 : ℝ) ≤ 2 * Real.sqrt (780 : ℝ) := by
    have h4 : (55 : ℝ) ^ 2 ≤ 4 * (780 : ℝ) := by norm_num
    have h1 := (Real.le_sqrt (by positivity : (0 : ℝ) ≤ (55 : ℝ))
      (by positivity : (0 : ℝ) ≤ 4 * (780 : ℝ))).mpr h4
    have h2 : Real.sqrt (4 * (780 : ℝ)) = 2 * Real.sqrt (780 : ℝ) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 2) (780 : ℝ),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    rwa [h2] at h1
  have hsT : 55 ≤ 780 := by norm_num
  have hsub : ((780 - 55 : ℕ) : ℝ) = (780 : ℝ) - (55 : ℝ) := by
    rw [Nat.cast_sub hsT]
    norm_num
  have hstep : (780 : ℝ) - 2 * Real.sqrt (780 : ℝ) ≤ ((780 - 55 : ℕ) : ℝ) := by
    rw [hsub]
    linarith [hfloor]
  have hsumI : (780 - 55) * 10 ^ 4 < ∑ p ∈ plist.filter (· ≤ 760), clbZ p := by
    rw [hplistLit3]
    decide
  have hsumR : ((780 - 55 : ℕ) : ℝ) <
      (∑ p ∈ plist.filter (· ≤ 760), (clbZ p : ℝ)) / 10 ^ 4 := by
    have h1 : ((780 - 55 : ℕ) : ℝ) * 10 ^ 4
        < ∑ p ∈ plist.filter (· ≤ 760), (clbZ p : ℝ) := by
      have h2 : ((780 - 55) * 10 ^ 4 : ℕ) < ∑ p ∈ plist.filter (· ≤ 760), clbZ p := hsumI
      exact_mod_cast h2
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
    exact h1
  calc (780 : ℝ) - 2 * Real.sqrt (780 : ℝ) ≤ ((780 - 55 : ℕ) : ℝ) := hstep
    _ < (∑ p ∈ plist.filter (· ≤ 760), (clbZ p : ℝ)) / 10 ^ 4 := hsumR
    _ ≤ ∑ p ∈ plist.filter (· ≤ 760), Real.log p := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
        calc (∑ p ∈ plist.filter (· ≤ 760), (clbZ p : ℝ))
            ≤ ∑ p ∈ plist.filter (· ≤ 760), Real.log p * 10 ^ 4 :=
              Finset.sum_le_sum (fun p hp => theta_cert_clbZ_le_log p (Finset.mem_of_mem_filter p hp))
          _ = (∑ p ∈ plist.filter (· ≤ 760), Real.log p) * 10 ^ 4 := by rw [Finset.sum_mul]
    _ = Chebyshev.theta ((760 : ℕ) : ℝ) := by
        rw [Chebyshev.theta_eq_sum_primesLE_log 760, theta_cert_primesLE_eq 760 (by norm_num)]

lemma blk_41 : ((801 : ℕ) : ℝ) - 2 * Real.sqrt ((801 : ℕ) : ℝ) < Chebyshev.theta ((780 : ℕ) : ℝ) := by
  have hfloor : (56 : ℝ) ≤ 2 * Real.sqrt (801 : ℝ) := by
    have h4 : (56 : ℝ) ^ 2 ≤ 4 * (801 : ℝ) := by norm_num
    have h1 := (Real.le_sqrt (by positivity : (0 : ℝ) ≤ (56 : ℝ))
      (by positivity : (0 : ℝ) ≤ 4 * (801 : ℝ))).mpr h4
    have h2 : Real.sqrt (4 * (801 : ℝ)) = 2 * Real.sqrt (801 : ℝ) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 2) (801 : ℝ),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    rwa [h2] at h1
  have hsT : 56 ≤ 801 := by norm_num
  have hsub : ((801 - 56 : ℕ) : ℝ) = (801 : ℝ) - (56 : ℝ) := by
    rw [Nat.cast_sub hsT]
    norm_num
  have hstep : (801 : ℝ) - 2 * Real.sqrt (801 : ℝ) ≤ ((801 - 56 : ℕ) : ℝ) := by
    rw [hsub]
    linarith [hfloor]
  have hsumI : (801 - 56) * 10 ^ 4 < ∑ p ∈ plist.filter (· ≤ 780), clbZ p := by
    rw [hplistLit3]
    decide
  have hsumR : ((801 - 56 : ℕ) : ℝ) <
      (∑ p ∈ plist.filter (· ≤ 780), (clbZ p : ℝ)) / 10 ^ 4 := by
    have h1 : ((801 - 56 : ℕ) : ℝ) * 10 ^ 4
        < ∑ p ∈ plist.filter (· ≤ 780), (clbZ p : ℝ) := by
      have h2 : ((801 - 56) * 10 ^ 4 : ℕ) < ∑ p ∈ plist.filter (· ≤ 780), clbZ p := hsumI
      exact_mod_cast h2
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
    exact h1
  calc (801 : ℝ) - 2 * Real.sqrt (801 : ℝ) ≤ ((801 - 56 : ℕ) : ℝ) := hstep
    _ < (∑ p ∈ plist.filter (· ≤ 780), (clbZ p : ℝ)) / 10 ^ 4 := hsumR
    _ ≤ ∑ p ∈ plist.filter (· ≤ 780), Real.log p := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
        calc (∑ p ∈ plist.filter (· ≤ 780), (clbZ p : ℝ))
            ≤ ∑ p ∈ plist.filter (· ≤ 780), Real.log p * 10 ^ 4 :=
              Finset.sum_le_sum (fun p hp => theta_cert_clbZ_le_log p (Finset.mem_of_mem_filter p hp))
          _ = (∑ p ∈ plist.filter (· ≤ 780), Real.log p) * 10 ^ 4 := by rw [Finset.sum_mul]
    _ = Chebyshev.theta ((780 : ℕ) : ℝ) := by
        rw [Chebyshev.theta_eq_sum_primesLE_log 780, theta_cert_primesLE_eq 780 (by norm_num)]

lemma blk_42 : ((816 : ℕ) : ℝ) - 2 * Real.sqrt ((816 : ℕ) : ℝ) < Chebyshev.theta ((801 : ℕ) : ℝ) := by
  have hfloor : (57 : ℝ) ≤ 2 * Real.sqrt (816 : ℝ) := by
    have h4 : (57 : ℝ) ^ 2 ≤ 4 * (816 : ℝ) := by norm_num
    have h1 := (Real.le_sqrt (by positivity : (0 : ℝ) ≤ (57 : ℝ))
      (by positivity : (0 : ℝ) ≤ 4 * (816 : ℝ))).mpr h4
    have h2 : Real.sqrt (4 * (816 : ℝ)) = 2 * Real.sqrt (816 : ℝ) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 2) (816 : ℝ),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    rwa [h2] at h1
  have hsT : 57 ≤ 816 := by norm_num
  have hsub : ((816 - 57 : ℕ) : ℝ) = (816 : ℝ) - (57 : ℝ) := by
    rw [Nat.cast_sub hsT]
    norm_num
  have hstep : (816 : ℝ) - 2 * Real.sqrt (816 : ℝ) ≤ ((816 - 57 : ℕ) : ℝ) := by
    rw [hsub]
    linarith [hfloor]
  have hsumI : (816 - 57) * 10 ^ 4 < ∑ p ∈ plist.filter (· ≤ 801), clbZ p := by
    rw [hplistLit3]
    decide
  have hsumR : ((816 - 57 : ℕ) : ℝ) <
      (∑ p ∈ plist.filter (· ≤ 801), (clbZ p : ℝ)) / 10 ^ 4 := by
    have h1 : ((816 - 57 : ℕ) : ℝ) * 10 ^ 4
        < ∑ p ∈ plist.filter (· ≤ 801), (clbZ p : ℝ) := by
      have h2 : ((816 - 57) * 10 ^ 4 : ℕ) < ∑ p ∈ plist.filter (· ≤ 801), clbZ p := hsumI
      exact_mod_cast h2
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
    exact h1
  calc (816 : ℝ) - 2 * Real.sqrt (816 : ℝ) ≤ ((816 - 57 : ℕ) : ℝ) := hstep
    _ < (∑ p ∈ plist.filter (· ≤ 801), (clbZ p : ℝ)) / 10 ^ 4 := hsumR
    _ ≤ ∑ p ∈ plist.filter (· ≤ 801), Real.log p := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
        calc (∑ p ∈ plist.filter (· ≤ 801), (clbZ p : ℝ))
            ≤ ∑ p ∈ plist.filter (· ≤ 801), Real.log p * 10 ^ 4 :=
              Finset.sum_le_sum (fun p hp => theta_cert_clbZ_le_log p (Finset.mem_of_mem_filter p hp))
          _ = (∑ p ∈ plist.filter (· ≤ 801), Real.log p) * 10 ^ 4 := by rw [Finset.sum_mul]
    _ = Chebyshev.theta ((801 : ℕ) : ℝ) := by
        rw [Chebyshev.theta_eq_sum_primesLE_log 801, theta_cert_primesLE_eq 801 (by norm_num)]

lemma blk_43 : ((829 : ℕ) : ℝ) - 2 * Real.sqrt ((829 : ℕ) : ℝ) < Chebyshev.theta ((816 : ℕ) : ℝ) := by
  have hfloor : (57 : ℝ) ≤ 2 * Real.sqrt (829 : ℝ) := by
    have h4 : (57 : ℝ) ^ 2 ≤ 4 * (829 : ℝ) := by norm_num
    have h1 := (Real.le_sqrt (by positivity : (0 : ℝ) ≤ (57 : ℝ))
      (by positivity : (0 : ℝ) ≤ 4 * (829 : ℝ))).mpr h4
    have h2 : Real.sqrt (4 * (829 : ℝ)) = 2 * Real.sqrt (829 : ℝ) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 2) (829 : ℝ),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    rwa [h2] at h1
  have hsT : 57 ≤ 829 := by norm_num
  have hsub : ((829 - 57 : ℕ) : ℝ) = (829 : ℝ) - (57 : ℝ) := by
    rw [Nat.cast_sub hsT]
    norm_num
  have hstep : (829 : ℝ) - 2 * Real.sqrt (829 : ℝ) ≤ ((829 - 57 : ℕ) : ℝ) := by
    rw [hsub]
    linarith [hfloor]
  have hsumI : (829 - 57) * 10 ^ 4 < ∑ p ∈ plist.filter (· ≤ 816), clbZ p := by
    rw [hplistLit3]
    decide
  have hsumR : ((829 - 57 : ℕ) : ℝ) <
      (∑ p ∈ plist.filter (· ≤ 816), (clbZ p : ℝ)) / 10 ^ 4 := by
    have h1 : ((829 - 57 : ℕ) : ℝ) * 10 ^ 4
        < ∑ p ∈ plist.filter (· ≤ 816), (clbZ p : ℝ) := by
      have h2 : ((829 - 57) * 10 ^ 4 : ℕ) < ∑ p ∈ plist.filter (· ≤ 816), clbZ p := hsumI
      exact_mod_cast h2
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
    exact h1
  calc (829 : ℝ) - 2 * Real.sqrt (829 : ℝ) ≤ ((829 - 57 : ℕ) : ℝ) := hstep
    _ < (∑ p ∈ plist.filter (· ≤ 816), (clbZ p : ℝ)) / 10 ^ 4 := hsumR
    _ ≤ ∑ p ∈ plist.filter (· ≤ 816), Real.log p := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
        calc (∑ p ∈ plist.filter (· ≤ 816), (clbZ p : ℝ))
            ≤ ∑ p ∈ plist.filter (· ≤ 816), Real.log p * 10 ^ 4 :=
              Finset.sum_le_sum (fun p hp => theta_cert_clbZ_le_log p (Finset.mem_of_mem_filter p hp))
          _ = (∑ p ∈ plist.filter (· ≤ 816), Real.log p) * 10 ^ 4 := by rw [Finset.sum_mul]
    _ = Chebyshev.theta ((816 : ℕ) : ℝ) := by
        rw [Chebyshev.theta_eq_sum_primesLE_log 816, theta_cert_primesLE_eq 816 (by norm_num)]

lemma blk_44 : ((857 : ℕ) : ℝ) - 2 * Real.sqrt ((857 : ℕ) : ℝ) < Chebyshev.theta ((829 : ℕ) : ℝ) := by
  have hfloor : (58 : ℝ) ≤ 2 * Real.sqrt (857 : ℝ) := by
    have h4 : (58 : ℝ) ^ 2 ≤ 4 * (857 : ℝ) := by norm_num
    have h1 := (Real.le_sqrt (by positivity : (0 : ℝ) ≤ (58 : ℝ))
      (by positivity : (0 : ℝ) ≤ 4 * (857 : ℝ))).mpr h4
    have h2 : Real.sqrt (4 * (857 : ℝ)) = 2 * Real.sqrt (857 : ℝ) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 2) (857 : ℝ),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    rwa [h2] at h1
  have hsT : 58 ≤ 857 := by norm_num
  have hsub : ((857 - 58 : ℕ) : ℝ) = (857 : ℝ) - (58 : ℝ) := by
    rw [Nat.cast_sub hsT]
    norm_num
  have hstep : (857 : ℝ) - 2 * Real.sqrt (857 : ℝ) ≤ ((857 - 58 : ℕ) : ℝ) := by
    rw [hsub]
    linarith [hfloor]
  have hsumI : (857 - 58) * 10 ^ 4 < ∑ p ∈ plist.filter (· ≤ 829), clbZ p := by
    rw [hplistLit3]
    decide
  have hsumR : ((857 - 58 : ℕ) : ℝ) <
      (∑ p ∈ plist.filter (· ≤ 829), (clbZ p : ℝ)) / 10 ^ 4 := by
    have h1 : ((857 - 58 : ℕ) : ℝ) * 10 ^ 4
        < ∑ p ∈ plist.filter (· ≤ 829), (clbZ p : ℝ) := by
      have h2 : ((857 - 58) * 10 ^ 4 : ℕ) < ∑ p ∈ plist.filter (· ≤ 829), clbZ p := hsumI
      exact_mod_cast h2
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
    exact h1
  calc (857 : ℝ) - 2 * Real.sqrt (857 : ℝ) ≤ ((857 - 58 : ℕ) : ℝ) := hstep
    _ < (∑ p ∈ plist.filter (· ≤ 829), (clbZ p : ℝ)) / 10 ^ 4 := hsumR
    _ ≤ ∑ p ∈ plist.filter (· ≤ 829), Real.log p := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
        calc (∑ p ∈ plist.filter (· ≤ 829), (clbZ p : ℝ))
            ≤ ∑ p ∈ plist.filter (· ≤ 829), Real.log p * 10 ^ 4 :=
              Finset.sum_le_sum (fun p hp => theta_cert_clbZ_le_log p (Finset.mem_of_mem_filter p hp))
          _ = (∑ p ∈ plist.filter (· ≤ 829), Real.log p) * 10 ^ 4 := by rw [Finset.sum_mul]
    _ = Chebyshev.theta ((829 : ℕ) : ℝ) := by
        rw [Chebyshev.theta_eq_sum_primesLE_log 829, theta_cert_primesLE_eq 829 (by norm_num)]

lemma blk_45 : ((878 : ℕ) : ℝ) - 2 * Real.sqrt ((878 : ℕ) : ℝ) < Chebyshev.theta ((857 : ℕ) : ℝ) := by
  have hfloor : (59 : ℝ) ≤ 2 * Real.sqrt (878 : ℝ) := by
    have h4 : (59 : ℝ) ^ 2 ≤ 4 * (878 : ℝ) := by norm_num
    have h1 := (Real.le_sqrt (by positivity : (0 : ℝ) ≤ (59 : ℝ))
      (by positivity : (0 : ℝ) ≤ 4 * (878 : ℝ))).mpr h4
    have h2 : Real.sqrt (4 * (878 : ℝ)) = 2 * Real.sqrt (878 : ℝ) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 2) (878 : ℝ),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    rwa [h2] at h1
  have hsT : 59 ≤ 878 := by norm_num
  have hsub : ((878 - 59 : ℕ) : ℝ) = (878 : ℝ) - (59 : ℝ) := by
    rw [Nat.cast_sub hsT]
    norm_num
  have hstep : (878 : ℝ) - 2 * Real.sqrt (878 : ℝ) ≤ ((878 - 59 : ℕ) : ℝ) := by
    rw [hsub]
    linarith [hfloor]
  have hsumI : (878 - 59) * 10 ^ 4 < ∑ p ∈ plist.filter (· ≤ 857), clbZ p := by
    rw [hplistLit3]
    decide
  have hsumR : ((878 - 59 : ℕ) : ℝ) <
      (∑ p ∈ plist.filter (· ≤ 857), (clbZ p : ℝ)) / 10 ^ 4 := by
    have h1 : ((878 - 59 : ℕ) : ℝ) * 10 ^ 4
        < ∑ p ∈ plist.filter (· ≤ 857), (clbZ p : ℝ) := by
      have h2 : ((878 - 59) * 10 ^ 4 : ℕ) < ∑ p ∈ plist.filter (· ≤ 857), clbZ p := hsumI
      exact_mod_cast h2
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
    exact h1
  calc (878 : ℝ) - 2 * Real.sqrt (878 : ℝ) ≤ ((878 - 59 : ℕ) : ℝ) := hstep
    _ < (∑ p ∈ plist.filter (· ≤ 857), (clbZ p : ℝ)) / 10 ^ 4 := hsumR
    _ ≤ ∑ p ∈ plist.filter (· ≤ 857), Real.log p := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
        calc (∑ p ∈ plist.filter (· ≤ 857), (clbZ p : ℝ))
            ≤ ∑ p ∈ plist.filter (· ≤ 857), Real.log p * 10 ^ 4 :=
              Finset.sum_le_sum (fun p hp => theta_cert_clbZ_le_log p (Finset.mem_of_mem_filter p hp))
          _ = (∑ p ∈ plist.filter (· ≤ 857), Real.log p) * 10 ^ 4 := by rw [Finset.sum_mul]
    _ = Chebyshev.theta ((857 : ℕ) : ℝ) := by
        rw [Chebyshev.theta_eq_sum_primesLE_log 857, theta_cert_primesLE_eq 857 (by norm_num)]

lemma blk_46 : ((898 : ℕ) : ℝ) - 2 * Real.sqrt ((898 : ℕ) : ℝ) < Chebyshev.theta ((878 : ℕ) : ℝ) := by
  have hfloor : (59 : ℝ) ≤ 2 * Real.sqrt (898 : ℝ) := by
    have h4 : (59 : ℝ) ^ 2 ≤ 4 * (898 : ℝ) := by norm_num
    have h1 := (Real.le_sqrt (by positivity : (0 : ℝ) ≤ (59 : ℝ))
      (by positivity : (0 : ℝ) ≤ 4 * (898 : ℝ))).mpr h4
    have h2 : Real.sqrt (4 * (898 : ℝ)) = 2 * Real.sqrt (898 : ℝ) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 2) (898 : ℝ),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    rwa [h2] at h1
  have hsT : 59 ≤ 898 := by norm_num
  have hsub : ((898 - 59 : ℕ) : ℝ) = (898 : ℝ) - (59 : ℝ) := by
    rw [Nat.cast_sub hsT]
    norm_num
  have hstep : (898 : ℝ) - 2 * Real.sqrt (898 : ℝ) ≤ ((898 - 59 : ℕ) : ℝ) := by
    rw [hsub]
    linarith [hfloor]
  have hsumI : (898 - 59) * 10 ^ 4 < ∑ p ∈ plist.filter (· ≤ 878), clbZ p := by
    rw [hplistLit3]
    decide
  have hsumR : ((898 - 59 : ℕ) : ℝ) <
      (∑ p ∈ plist.filter (· ≤ 878), (clbZ p : ℝ)) / 10 ^ 4 := by
    have h1 : ((898 - 59 : ℕ) : ℝ) * 10 ^ 4
        < ∑ p ∈ plist.filter (· ≤ 878), (clbZ p : ℝ) := by
      have h2 : ((898 - 59) * 10 ^ 4 : ℕ) < ∑ p ∈ plist.filter (· ≤ 878), clbZ p := hsumI
      exact_mod_cast h2
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
    exact h1
  calc (898 : ℝ) - 2 * Real.sqrt (898 : ℝ) ≤ ((898 - 59 : ℕ) : ℝ) := hstep
    _ < (∑ p ∈ plist.filter (· ≤ 878), (clbZ p : ℝ)) / 10 ^ 4 := hsumR
    _ ≤ ∑ p ∈ plist.filter (· ≤ 878), Real.log p := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
        calc (∑ p ∈ plist.filter (· ≤ 878), (clbZ p : ℝ))
            ≤ ∑ p ∈ plist.filter (· ≤ 878), Real.log p * 10 ^ 4 :=
              Finset.sum_le_sum (fun p hp => theta_cert_clbZ_le_log p (Finset.mem_of_mem_filter p hp))
          _ = (∑ p ∈ plist.filter (· ≤ 878), Real.log p) * 10 ^ 4 := by rw [Finset.sum_mul]
    _ = Chebyshev.theta ((878 : ℕ) : ℝ) := by
        rw [Chebyshev.theta_eq_sum_primesLE_log 878, theta_cert_primesLE_eq 878 (by norm_num)]

lemma blk_47 : ((920 : ℕ) : ℝ) - 2 * Real.sqrt ((920 : ℕ) : ℝ) < Chebyshev.theta ((898 : ℕ) : ℝ) := by
  have hfloor : (60 : ℝ) ≤ 2 * Real.sqrt (920 : ℝ) := by
    have h4 : (60 : ℝ) ^ 2 ≤ 4 * (920 : ℝ) := by norm_num
    have h1 := (Real.le_sqrt (by positivity : (0 : ℝ) ≤ (60 : ℝ))
      (by positivity : (0 : ℝ) ≤ 4 * (920 : ℝ))).mpr h4
    have h2 : Real.sqrt (4 * (920 : ℝ)) = 2 * Real.sqrt (920 : ℝ) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 2) (920 : ℝ),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    rwa [h2] at h1
  have hsT : 60 ≤ 920 := by norm_num
  have hsub : ((920 - 60 : ℕ) : ℝ) = (920 : ℝ) - (60 : ℝ) := by
    rw [Nat.cast_sub hsT]
    norm_num
  have hstep : (920 : ℝ) - 2 * Real.sqrt (920 : ℝ) ≤ ((920 - 60 : ℕ) : ℝ) := by
    rw [hsub]
    linarith [hfloor]
  have hsumI : (920 - 60) * 10 ^ 4 < ∑ p ∈ plist.filter (· ≤ 898), clbZ p := by
    rw [hplistLit3]
    decide
  have hsumR : ((920 - 60 : ℕ) : ℝ) <
      (∑ p ∈ plist.filter (· ≤ 898), (clbZ p : ℝ)) / 10 ^ 4 := by
    have h1 : ((920 - 60 : ℕ) : ℝ) * 10 ^ 4
        < ∑ p ∈ plist.filter (· ≤ 898), (clbZ p : ℝ) := by
      have h2 : ((920 - 60) * 10 ^ 4 : ℕ) < ∑ p ∈ plist.filter (· ≤ 898), clbZ p := hsumI
      exact_mod_cast h2
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
    exact h1
  calc (920 : ℝ) - 2 * Real.sqrt (920 : ℝ) ≤ ((920 - 60 : ℕ) : ℝ) := hstep
    _ < (∑ p ∈ plist.filter (· ≤ 898), (clbZ p : ℝ)) / 10 ^ 4 := hsumR
    _ ≤ ∑ p ∈ plist.filter (· ≤ 898), Real.log p := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
        calc (∑ p ∈ plist.filter (· ≤ 898), (clbZ p : ℝ))
            ≤ ∑ p ∈ plist.filter (· ≤ 898), Real.log p * 10 ^ 4 :=
              Finset.sum_le_sum (fun p hp => theta_cert_clbZ_le_log p (Finset.mem_of_mem_filter p hp))
          _ = (∑ p ∈ plist.filter (· ≤ 898), Real.log p) * 10 ^ 4 := by rw [Finset.sum_mul]
    _ = Chebyshev.theta ((898 : ℕ) : ℝ) := by
        rw [Chebyshev.theta_eq_sum_primesLE_log 898, theta_cert_primesLE_eq 898 (by norm_num)]

lemma blk_48 : ((941 : ℕ) : ℝ) - 2 * Real.sqrt ((941 : ℕ) : ℝ) < Chebyshev.theta ((920 : ℕ) : ℝ) := by
  have hfloor : (61 : ℝ) ≤ 2 * Real.sqrt (941 : ℝ) := by
    have h4 : (61 : ℝ) ^ 2 ≤ 4 * (941 : ℝ) := by norm_num
    have h1 := (Real.le_sqrt (by positivity : (0 : ℝ) ≤ (61 : ℝ))
      (by positivity : (0 : ℝ) ≤ 4 * (941 : ℝ))).mpr h4
    have h2 : Real.sqrt (4 * (941 : ℝ)) = 2 * Real.sqrt (941 : ℝ) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 2) (941 : ℝ),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    rwa [h2] at h1
  have hsT : 61 ≤ 941 := by norm_num
  have hsub : ((941 - 61 : ℕ) : ℝ) = (941 : ℝ) - (61 : ℝ) := by
    rw [Nat.cast_sub hsT]
    norm_num
  have hstep : (941 : ℝ) - 2 * Real.sqrt (941 : ℝ) ≤ ((941 - 61 : ℕ) : ℝ) := by
    rw [hsub]
    linarith [hfloor]
  have hsumI : (941 - 61) * 10 ^ 4 < ∑ p ∈ plist.filter (· ≤ 920), clbZ p := by
    rw [hplistLit3]
    decide
  have hsumR : ((941 - 61 : ℕ) : ℝ) <
      (∑ p ∈ plist.filter (· ≤ 920), (clbZ p : ℝ)) / 10 ^ 4 := by
    have h1 : ((941 - 61 : ℕ) : ℝ) * 10 ^ 4
        < ∑ p ∈ plist.filter (· ≤ 920), (clbZ p : ℝ) := by
      have h2 : ((941 - 61) * 10 ^ 4 : ℕ) < ∑ p ∈ plist.filter (· ≤ 920), clbZ p := hsumI
      exact_mod_cast h2
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
    exact h1
  calc (941 : ℝ) - 2 * Real.sqrt (941 : ℝ) ≤ ((941 - 61 : ℕ) : ℝ) := hstep
    _ < (∑ p ∈ plist.filter (· ≤ 920), (clbZ p : ℝ)) / 10 ^ 4 := hsumR
    _ ≤ ∑ p ∈ plist.filter (· ≤ 920), Real.log p := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
        calc (∑ p ∈ plist.filter (· ≤ 920), (clbZ p : ℝ))
            ≤ ∑ p ∈ plist.filter (· ≤ 920), Real.log p * 10 ^ 4 :=
              Finset.sum_le_sum (fun p hp => theta_cert_clbZ_le_log p (Finset.mem_of_mem_filter p hp))
          _ = (∑ p ∈ plist.filter (· ≤ 920), Real.log p) * 10 ^ 4 := by rw [Finset.sum_mul]
    _ = Chebyshev.theta ((920 : ℕ) : ℝ) := by
        rw [Chebyshev.theta_eq_sum_primesLE_log 920, theta_cert_primesLE_eq 920 (by norm_num)]

lemma blk_49 : ((963 : ℕ) : ℝ) - 2 * Real.sqrt ((963 : ℕ) : ℝ) < Chebyshev.theta ((941 : ℕ) : ℝ) := by
  have hfloor : (62 : ℝ) ≤ 2 * Real.sqrt (963 : ℝ) := by
    have h4 : (62 : ℝ) ^ 2 ≤ 4 * (963 : ℝ) := by norm_num
    have h1 := (Real.le_sqrt (by positivity : (0 : ℝ) ≤ (62 : ℝ))
      (by positivity : (0 : ℝ) ≤ 4 * (963 : ℝ))).mpr h4
    have h2 : Real.sqrt (4 * (963 : ℝ)) = 2 * Real.sqrt (963 : ℝ) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 2) (963 : ℝ),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    rwa [h2] at h1
  have hsT : 62 ≤ 963 := by norm_num
  have hsub : ((963 - 62 : ℕ) : ℝ) = (963 : ℝ) - (62 : ℝ) := by
    rw [Nat.cast_sub hsT]
    norm_num
  have hstep : (963 : ℝ) - 2 * Real.sqrt (963 : ℝ) ≤ ((963 - 62 : ℕ) : ℝ) := by
    rw [hsub]
    linarith [hfloor]
  have hsumI : (963 - 62) * 10 ^ 4 < ∑ p ∈ plist.filter (· ≤ 941), clbZ p := by
    rw [hplistLit3]
    decide
  have hsumR : ((963 - 62 : ℕ) : ℝ) <
      (∑ p ∈ plist.filter (· ≤ 941), (clbZ p : ℝ)) / 10 ^ 4 := by
    have h1 : ((963 - 62 : ℕ) : ℝ) * 10 ^ 4
        < ∑ p ∈ plist.filter (· ≤ 941), (clbZ p : ℝ) := by
      have h2 : ((963 - 62) * 10 ^ 4 : ℕ) < ∑ p ∈ plist.filter (· ≤ 941), clbZ p := hsumI
      exact_mod_cast h2
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
    exact h1
  calc (963 : ℝ) - 2 * Real.sqrt (963 : ℝ) ≤ ((963 - 62 : ℕ) : ℝ) := hstep
    _ < (∑ p ∈ plist.filter (· ≤ 941), (clbZ p : ℝ)) / 10 ^ 4 := hsumR
    _ ≤ ∑ p ∈ plist.filter (· ≤ 941), Real.log p := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
        calc (∑ p ∈ plist.filter (· ≤ 941), (clbZ p : ℝ))
            ≤ ∑ p ∈ plist.filter (· ≤ 941), Real.log p * 10 ^ 4 :=
              Finset.sum_le_sum (fun p hp => theta_cert_clbZ_le_log p (Finset.mem_of_mem_filter p hp))
          _ = (∑ p ∈ plist.filter (· ≤ 941), Real.log p) * 10 ^ 4 := by rw [Finset.sum_mul]
    _ = Chebyshev.theta ((941 : ℕ) : ℝ) := by
        rw [Chebyshev.theta_eq_sum_primesLE_log 941, theta_cert_primesLE_eq 941 (by norm_num)]

lemma blk_50 : ((976 : ℕ) : ℝ) - 2 * Real.sqrt ((976 : ℕ) : ℝ) < Chebyshev.theta ((963 : ℕ) : ℝ) := by
  have hfloor : (62 : ℝ) ≤ 2 * Real.sqrt (976 : ℝ) := by
    have h4 : (62 : ℝ) ^ 2 ≤ 4 * (976 : ℝ) := by norm_num
    have h1 := (Real.le_sqrt (by positivity : (0 : ℝ) ≤ (62 : ℝ))
      (by positivity : (0 : ℝ) ≤ 4 * (976 : ℝ))).mpr h4
    have h2 : Real.sqrt (4 * (976 : ℝ)) = 2 * Real.sqrt (976 : ℝ) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 2) (976 : ℝ),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    rwa [h2] at h1
  have hsT : 62 ≤ 976 := by norm_num
  have hsub : ((976 - 62 : ℕ) : ℝ) = (976 : ℝ) - (62 : ℝ) := by
    rw [Nat.cast_sub hsT]
    norm_num
  have hstep : (976 : ℝ) - 2 * Real.sqrt (976 : ℝ) ≤ ((976 - 62 : ℕ) : ℝ) := by
    rw [hsub]
    linarith [hfloor]
  have hsumI : (976 - 62) * 10 ^ 4 < ∑ p ∈ plist.filter (· ≤ 963), clbZ p := by
    rw [hplistLit3]
    decide
  have hsumR : ((976 - 62 : ℕ) : ℝ) <
      (∑ p ∈ plist.filter (· ≤ 963), (clbZ p : ℝ)) / 10 ^ 4 := by
    have h1 : ((976 - 62 : ℕ) : ℝ) * 10 ^ 4
        < ∑ p ∈ plist.filter (· ≤ 963), (clbZ p : ℝ) := by
      have h2 : ((976 - 62) * 10 ^ 4 : ℕ) < ∑ p ∈ plist.filter (· ≤ 963), clbZ p := hsumI
      exact_mod_cast h2
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
    exact h1
  calc (976 : ℝ) - 2 * Real.sqrt (976 : ℝ) ≤ ((976 - 62 : ℕ) : ℝ) := hstep
    _ < (∑ p ∈ plist.filter (· ≤ 963), (clbZ p : ℝ)) / 10 ^ 4 := hsumR
    _ ≤ ∑ p ∈ plist.filter (· ≤ 963), Real.log p := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
        calc (∑ p ∈ plist.filter (· ≤ 963), (clbZ p : ℝ))
            ≤ ∑ p ∈ plist.filter (· ≤ 963), Real.log p * 10 ^ 4 :=
              Finset.sum_le_sum (fun p hp => theta_cert_clbZ_le_log p (Finset.mem_of_mem_filter p hp))
          _ = (∑ p ∈ plist.filter (· ≤ 963), Real.log p) * 10 ^ 4 := by rw [Finset.sum_mul]
    _ = Chebyshev.theta ((963 : ℕ) : ℝ) := by
        rw [Chebyshev.theta_eq_sum_primesLE_log 963, theta_cert_primesLE_eq 963 (by norm_num)]

lemma blk_51 : ((990 : ℕ) : ℝ) - 2 * Real.sqrt ((990 : ℕ) : ℝ) < Chebyshev.theta ((976 : ℕ) : ℝ) := by
  have hfloor : (62 : ℝ) ≤ 2 * Real.sqrt (990 : ℝ) := by
    have h4 : (62 : ℝ) ^ 2 ≤ 4 * (990 : ℝ) := by norm_num
    have h1 := (Real.le_sqrt (by positivity : (0 : ℝ) ≤ (62 : ℝ))
      (by positivity : (0 : ℝ) ≤ 4 * (990 : ℝ))).mpr h4
    have h2 : Real.sqrt (4 * (990 : ℝ)) = 2 * Real.sqrt (990 : ℝ) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 2) (990 : ℝ),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    rwa [h2] at h1
  have hsT : 62 ≤ 990 := by norm_num
  have hsub : ((990 - 62 : ℕ) : ℝ) = (990 : ℝ) - (62 : ℝ) := by
    rw [Nat.cast_sub hsT]
    norm_num
  have hstep : (990 : ℝ) - 2 * Real.sqrt (990 : ℝ) ≤ ((990 - 62 : ℕ) : ℝ) := by
    rw [hsub]
    linarith [hfloor]
  have hsumI : (990 - 62) * 10 ^ 4 < ∑ p ∈ plist.filter (· ≤ 976), clbZ p := by
    rw [hplistLit3]
    decide
  have hsumR : ((990 - 62 : ℕ) : ℝ) <
      (∑ p ∈ plist.filter (· ≤ 976), (clbZ p : ℝ)) / 10 ^ 4 := by
    have h1 : ((990 - 62 : ℕ) : ℝ) * 10 ^ 4
        < ∑ p ∈ plist.filter (· ≤ 976), (clbZ p : ℝ) := by
      have h2 : ((990 - 62) * 10 ^ 4 : ℕ) < ∑ p ∈ plist.filter (· ≤ 976), clbZ p := hsumI
      exact_mod_cast h2
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
    exact h1
  calc (990 : ℝ) - 2 * Real.sqrt (990 : ℝ) ≤ ((990 - 62 : ℕ) : ℝ) := hstep
    _ < (∑ p ∈ plist.filter (· ≤ 976), (clbZ p : ℝ)) / 10 ^ 4 := hsumR
    _ ≤ ∑ p ∈ plist.filter (· ≤ 976), Real.log p := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
        calc (∑ p ∈ plist.filter (· ≤ 976), (clbZ p : ℝ))
            ≤ ∑ p ∈ plist.filter (· ≤ 976), Real.log p * 10 ^ 4 :=
              Finset.sum_le_sum (fun p hp => theta_cert_clbZ_le_log p (Finset.mem_of_mem_filter p hp))
          _ = (∑ p ∈ plist.filter (· ≤ 976), Real.log p) * 10 ^ 4 := by rw [Finset.sum_mul]
    _ = Chebyshev.theta ((976 : ℕ) : ℝ) := by
        rw [Chebyshev.theta_eq_sum_primesLE_log 976, theta_cert_primesLE_eq 976 (by norm_num)]

lemma blk_52 : ((1005 : ℕ) : ℝ) - 2 * Real.sqrt ((1005 : ℕ) : ℝ) < Chebyshev.theta ((990 : ℕ) : ℝ) := by
  have hfloor : (63 : ℝ) ≤ 2 * Real.sqrt (1005 : ℝ) := by
    have h4 : (63 : ℝ) ^ 2 ≤ 4 * (1005 : ℝ) := by norm_num
    have h1 := (Real.le_sqrt (by positivity : (0 : ℝ) ≤ (63 : ℝ))
      (by positivity : (0 : ℝ) ≤ 4 * (1005 : ℝ))).mpr h4
    have h2 : Real.sqrt (4 * (1005 : ℝ)) = 2 * Real.sqrt (1005 : ℝ) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 2) (1005 : ℝ),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    rwa [h2] at h1
  have hsT : 63 ≤ 1005 := by norm_num
  have hsub : ((1005 - 63 : ℕ) : ℝ) = (1005 : ℝ) - (63 : ℝ) := by
    rw [Nat.cast_sub hsT]
    norm_num
  have hstep : (1005 : ℝ) - 2 * Real.sqrt (1005 : ℝ) ≤ ((1005 - 63 : ℕ) : ℝ) := by
    rw [hsub]
    linarith [hfloor]
  have hsumI : (1005 - 63) * 10 ^ 4 < ∑ p ∈ plist.filter (· ≤ 990), clbZ p := by
    rw [hplistLit3]
    decide
  have hsumR : ((1005 - 63 : ℕ) : ℝ) <
      (∑ p ∈ plist.filter (· ≤ 990), (clbZ p : ℝ)) / 10 ^ 4 := by
    have h1 : ((1005 - 63 : ℕ) : ℝ) * 10 ^ 4
        < ∑ p ∈ plist.filter (· ≤ 990), (clbZ p : ℝ) := by
      have h2 : ((1005 - 63) * 10 ^ 4 : ℕ) < ∑ p ∈ plist.filter (· ≤ 990), clbZ p := hsumI
      exact_mod_cast h2
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
    exact h1
  calc (1005 : ℝ) - 2 * Real.sqrt (1005 : ℝ) ≤ ((1005 - 63 : ℕ) : ℝ) := hstep
    _ < (∑ p ∈ plist.filter (· ≤ 990), (clbZ p : ℝ)) / 10 ^ 4 := hsumR
    _ ≤ ∑ p ∈ plist.filter (· ≤ 990), Real.log p := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
        calc (∑ p ∈ plist.filter (· ≤ 990), (clbZ p : ℝ))
            ≤ ∑ p ∈ plist.filter (· ≤ 990), Real.log p * 10 ^ 4 :=
              Finset.sum_le_sum (fun p hp => theta_cert_clbZ_le_log p (Finset.mem_of_mem_filter p hp))
          _ = (∑ p ∈ plist.filter (· ≤ 990), Real.log p) * 10 ^ 4 := by rw [Finset.sum_mul]
    _ = Chebyshev.theta ((990 : ℕ) : ℝ) := by
        rw [Chebyshev.theta_eq_sum_primesLE_log 990, theta_cert_primesLE_eq 990 (by norm_num)]


theorem solution (ab : ℕ × ℕ) (hab : ab ∈ blk3) :
    ((min (ab.2 + 1) 1420 : ℕ) : ℝ) - 2 * Real.sqrt ((min (ab.2 + 1) 1420 : ℕ) : ℝ) <
      Chebyshev.theta ((ab.1 : ℕ) : ℝ) := by
  have hmem := hab
  simp only [blk3, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals cases h
  all_goals (first | exact blk_35 | exact blk_36 | exact blk_37 | exact blk_38 | exact blk_39 | exact blk_40 | exact blk_41 | exact blk_42 | exact blk_43 | exact blk_44 | exact blk_45 | exact blk_46 | exact blk_47 | exact blk_48 | exact blk_49 | exact blk_50 | exact blk_51 | exact blk_52)

end TaoFivePrimes


open TaoFivePrimes

/-- The verification harness looks for `theorem solution` in the root
namespace, so the namespaced proof above is re-exported at the root. -/
theorem solution (ab : ℕ × ℕ) (hab : ab ∈ blk3) :
    ((min (ab.2 + 1) 1420 : ℕ) : ℝ) - 2 * Real.sqrt ((min (ab.2 + 1) 1420 : ℕ) : ℝ) <
      Chebyshev.theta ((ab.1 : ℕ) : ℝ) :=
  TaoFivePrimes.solution ab hab
