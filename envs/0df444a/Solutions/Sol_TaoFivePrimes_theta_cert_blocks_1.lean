-- Prove2me | solution 1 for TaoFivePrimes.theta_cert_blocks_1
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T14:23:03.454885+00:00
-- url     : https://prove2.me/submissions/9d28a475-8e5f-4a3b-89c0-c46f255829c1

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

def plistLit1 : Finset ℕ :=
  ⟨(↑([2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021, 1031, 1033, 1039, 1049, 1051, 1061, 1063, 1069, 1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163, 1171, 1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249, 1259, 1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367, 1373, 1381, 1399, 1409] : List ℕ) : Multiset ℕ), by decide⟩

lemma hplistLit1 : plist = plistLit1 := by decide

lemma blk_0 : ((264 : ℕ) : ℝ) - 2 * Real.sqrt ((264 : ℕ) : ℝ) < Chebyshev.theta ((255 : ℕ) : ℝ) := by
  have hfloor : (32 : ℝ) ≤ 2 * Real.sqrt (264 : ℝ) := by
    have h4 : (32 : ℝ) ^ 2 ≤ 4 * (264 : ℝ) := by norm_num
    have h1 := (Real.le_sqrt (by positivity : (0 : ℝ) ≤ (32 : ℝ))
      (by positivity : (0 : ℝ) ≤ 4 * (264 : ℝ))).mpr h4
    have h2 : Real.sqrt (4 * (264 : ℝ)) = 2 * Real.sqrt (264 : ℝ) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 2) (264 : ℝ),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    rwa [h2] at h1
  have hsT : 32 ≤ 264 := by norm_num
  have hsub : ((264 - 32 : ℕ) : ℝ) = (264 : ℝ) - (32 : ℝ) := by
    rw [Nat.cast_sub hsT]
    norm_num
  have hstep : (264 : ℝ) - 2 * Real.sqrt (264 : ℝ) ≤ ((264 - 32 : ℕ) : ℝ) := by
    rw [hsub]
    linarith [hfloor]
  have hsumI : (264 - 32) * 10 ^ 4 < ∑ p ∈ plist.filter (· ≤ 255), clbZ p := by
    rw [hplistLit1]
    decide
  have hsumR : ((264 - 32 : ℕ) : ℝ) <
      (∑ p ∈ plist.filter (· ≤ 255), (clbZ p : ℝ)) / 10 ^ 4 := by
    have h1 : ((264 - 32 : ℕ) : ℝ) * 10 ^ 4
        < ∑ p ∈ plist.filter (· ≤ 255), (clbZ p : ℝ) := by
      have h2 : ((264 - 32) * 10 ^ 4 : ℕ) < ∑ p ∈ plist.filter (· ≤ 255), clbZ p := hsumI
      exact_mod_cast h2
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
    exact h1
  calc (264 : ℝ) - 2 * Real.sqrt (264 : ℝ) ≤ ((264 - 32 : ℕ) : ℝ) := hstep
    _ < (∑ p ∈ plist.filter (· ≤ 255), (clbZ p : ℝ)) / 10 ^ 4 := hsumR
    _ ≤ ∑ p ∈ plist.filter (· ≤ 255), Real.log p := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
        calc (∑ p ∈ plist.filter (· ≤ 255), (clbZ p : ℝ))
            ≤ ∑ p ∈ plist.filter (· ≤ 255), Real.log p * 10 ^ 4 :=
              Finset.sum_le_sum (fun p hp => theta_cert_clbZ_le_log p (Finset.mem_of_mem_filter p hp))
          _ = (∑ p ∈ plist.filter (· ≤ 255), Real.log p) * 10 ^ 4 := by rw [Finset.sum_mul]
    _ = Chebyshev.theta ((255 : ℕ) : ℝ) := by
        rw [Chebyshev.theta_eq_sum_primesLE_log 255, theta_cert_primesLE_eq 255 (by norm_num)]

lemma blk_1 : ((276 : ℕ) : ℝ) - 2 * Real.sqrt ((276 : ℕ) : ℝ) < Chebyshev.theta ((264 : ℕ) : ℝ) := by
  have hfloor : (33 : ℝ) ≤ 2 * Real.sqrt (276 : ℝ) := by
    have h4 : (33 : ℝ) ^ 2 ≤ 4 * (276 : ℝ) := by norm_num
    have h1 := (Real.le_sqrt (by positivity : (0 : ℝ) ≤ (33 : ℝ))
      (by positivity : (0 : ℝ) ≤ 4 * (276 : ℝ))).mpr h4
    have h2 : Real.sqrt (4 * (276 : ℝ)) = 2 * Real.sqrt (276 : ℝ) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 2) (276 : ℝ),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    rwa [h2] at h1
  have hsT : 33 ≤ 276 := by norm_num
  have hsub : ((276 - 33 : ℕ) : ℝ) = (276 : ℝ) - (33 : ℝ) := by
    rw [Nat.cast_sub hsT]
    norm_num
  have hstep : (276 : ℝ) - 2 * Real.sqrt (276 : ℝ) ≤ ((276 - 33 : ℕ) : ℝ) := by
    rw [hsub]
    linarith [hfloor]
  have hsumI : (276 - 33) * 10 ^ 4 < ∑ p ∈ plist.filter (· ≤ 264), clbZ p := by
    rw [hplistLit1]
    decide
  have hsumR : ((276 - 33 : ℕ) : ℝ) <
      (∑ p ∈ plist.filter (· ≤ 264), (clbZ p : ℝ)) / 10 ^ 4 := by
    have h1 : ((276 - 33 : ℕ) : ℝ) * 10 ^ 4
        < ∑ p ∈ plist.filter (· ≤ 264), (clbZ p : ℝ) := by
      have h2 : ((276 - 33) * 10 ^ 4 : ℕ) < ∑ p ∈ plist.filter (· ≤ 264), clbZ p := hsumI
      exact_mod_cast h2
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
    exact h1
  calc (276 : ℝ) - 2 * Real.sqrt (276 : ℝ) ≤ ((276 - 33 : ℕ) : ℝ) := hstep
    _ < (∑ p ∈ plist.filter (· ≤ 264), (clbZ p : ℝ)) / 10 ^ 4 := hsumR
    _ ≤ ∑ p ∈ plist.filter (· ≤ 264), Real.log p := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
        calc (∑ p ∈ plist.filter (· ≤ 264), (clbZ p : ℝ))
            ≤ ∑ p ∈ plist.filter (· ≤ 264), Real.log p * 10 ^ 4 :=
              Finset.sum_le_sum (fun p hp => theta_cert_clbZ_le_log p (Finset.mem_of_mem_filter p hp))
          _ = (∑ p ∈ plist.filter (· ≤ 264), Real.log p) * 10 ^ 4 := by rw [Finset.sum_mul]
    _ = Chebyshev.theta ((264 : ℕ) : ℝ) := by
        rw [Chebyshev.theta_eq_sum_primesLE_log 264, theta_cert_primesLE_eq 264 (by norm_num)]

lemma blk_2 : ((287 : ℕ) : ℝ) - 2 * Real.sqrt ((287 : ℕ) : ℝ) < Chebyshev.theta ((276 : ℕ) : ℝ) := by
  have hfloor : (33 : ℝ) ≤ 2 * Real.sqrt (287 : ℝ) := by
    have h4 : (33 : ℝ) ^ 2 ≤ 4 * (287 : ℝ) := by norm_num
    have h1 := (Real.le_sqrt (by positivity : (0 : ℝ) ≤ (33 : ℝ))
      (by positivity : (0 : ℝ) ≤ 4 * (287 : ℝ))).mpr h4
    have h2 : Real.sqrt (4 * (287 : ℝ)) = 2 * Real.sqrt (287 : ℝ) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 2) (287 : ℝ),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    rwa [h2] at h1
  have hsT : 33 ≤ 287 := by norm_num
  have hsub : ((287 - 33 : ℕ) : ℝ) = (287 : ℝ) - (33 : ℝ) := by
    rw [Nat.cast_sub hsT]
    norm_num
  have hstep : (287 : ℝ) - 2 * Real.sqrt (287 : ℝ) ≤ ((287 - 33 : ℕ) : ℝ) := by
    rw [hsub]
    linarith [hfloor]
  have hsumI : (287 - 33) * 10 ^ 4 < ∑ p ∈ plist.filter (· ≤ 276), clbZ p := by
    rw [hplistLit1]
    decide
  have hsumR : ((287 - 33 : ℕ) : ℝ) <
      (∑ p ∈ plist.filter (· ≤ 276), (clbZ p : ℝ)) / 10 ^ 4 := by
    have h1 : ((287 - 33 : ℕ) : ℝ) * 10 ^ 4
        < ∑ p ∈ plist.filter (· ≤ 276), (clbZ p : ℝ) := by
      have h2 : ((287 - 33) * 10 ^ 4 : ℕ) < ∑ p ∈ plist.filter (· ≤ 276), clbZ p := hsumI
      exact_mod_cast h2
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
    exact h1
  calc (287 : ℝ) - 2 * Real.sqrt (287 : ℝ) ≤ ((287 - 33 : ℕ) : ℝ) := hstep
    _ < (∑ p ∈ plist.filter (· ≤ 276), (clbZ p : ℝ)) / 10 ^ 4 := hsumR
    _ ≤ ∑ p ∈ plist.filter (· ≤ 276), Real.log p := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
        calc (∑ p ∈ plist.filter (· ≤ 276), (clbZ p : ℝ))
            ≤ ∑ p ∈ plist.filter (· ≤ 276), Real.log p * 10 ^ 4 :=
              Finset.sum_le_sum (fun p hp => theta_cert_clbZ_le_log p (Finset.mem_of_mem_filter p hp))
          _ = (∑ p ∈ plist.filter (· ≤ 276), Real.log p) * 10 ^ 4 := by rw [Finset.sum_mul]
    _ = Chebyshev.theta ((276 : ℕ) : ℝ) := by
        rw [Chebyshev.theta_eq_sum_primesLE_log 276, theta_cert_primesLE_eq 276 (by norm_num)]

lemma blk_3 : ((305 : ℕ) : ℝ) - 2 * Real.sqrt ((305 : ℕ) : ℝ) < Chebyshev.theta ((287 : ℕ) : ℝ) := by
  have hfloor : (34 : ℝ) ≤ 2 * Real.sqrt (305 : ℝ) := by
    have h4 : (34 : ℝ) ^ 2 ≤ 4 * (305 : ℝ) := by norm_num
    have h1 := (Real.le_sqrt (by positivity : (0 : ℝ) ≤ (34 : ℝ))
      (by positivity : (0 : ℝ) ≤ 4 * (305 : ℝ))).mpr h4
    have h2 : Real.sqrt (4 * (305 : ℝ)) = 2 * Real.sqrt (305 : ℝ) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 2) (305 : ℝ),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    rwa [h2] at h1
  have hsT : 34 ≤ 305 := by norm_num
  have hsub : ((305 - 34 : ℕ) : ℝ) = (305 : ℝ) - (34 : ℝ) := by
    rw [Nat.cast_sub hsT]
    norm_num
  have hstep : (305 : ℝ) - 2 * Real.sqrt (305 : ℝ) ≤ ((305 - 34 : ℕ) : ℝ) := by
    rw [hsub]
    linarith [hfloor]
  have hsumI : (305 - 34) * 10 ^ 4 < ∑ p ∈ plist.filter (· ≤ 287), clbZ p := by
    rw [hplistLit1]
    decide
  have hsumR : ((305 - 34 : ℕ) : ℝ) <
      (∑ p ∈ plist.filter (· ≤ 287), (clbZ p : ℝ)) / 10 ^ 4 := by
    have h1 : ((305 - 34 : ℕ) : ℝ) * 10 ^ 4
        < ∑ p ∈ plist.filter (· ≤ 287), (clbZ p : ℝ) := by
      have h2 : ((305 - 34) * 10 ^ 4 : ℕ) < ∑ p ∈ plist.filter (· ≤ 287), clbZ p := hsumI
      exact_mod_cast h2
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
    exact h1
  calc (305 : ℝ) - 2 * Real.sqrt (305 : ℝ) ≤ ((305 - 34 : ℕ) : ℝ) := hstep
    _ < (∑ p ∈ plist.filter (· ≤ 287), (clbZ p : ℝ)) / 10 ^ 4 := hsumR
    _ ≤ ∑ p ∈ plist.filter (· ≤ 287), Real.log p := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
        calc (∑ p ∈ plist.filter (· ≤ 287), (clbZ p : ℝ))
            ≤ ∑ p ∈ plist.filter (· ≤ 287), Real.log p * 10 ^ 4 :=
              Finset.sum_le_sum (fun p hp => theta_cert_clbZ_le_log p (Finset.mem_of_mem_filter p hp))
          _ = (∑ p ∈ plist.filter (· ≤ 287), Real.log p) * 10 ^ 4 := by rw [Finset.sum_mul]
    _ = Chebyshev.theta ((287 : ℕ) : ℝ) := by
        rw [Chebyshev.theta_eq_sum_primesLE_log 287, theta_cert_primesLE_eq 287 (by norm_num)]

lemma blk_4 : ((312 : ℕ) : ℝ) - 2 * Real.sqrt ((312 : ℕ) : ℝ) < Chebyshev.theta ((305 : ℕ) : ℝ) := by
  have hfloor : (35 : ℝ) ≤ 2 * Real.sqrt (312 : ℝ) := by
    have h4 : (35 : ℝ) ^ 2 ≤ 4 * (312 : ℝ) := by norm_num
    have h1 := (Real.le_sqrt (by positivity : (0 : ℝ) ≤ (35 : ℝ))
      (by positivity : (0 : ℝ) ≤ 4 * (312 : ℝ))).mpr h4
    have h2 : Real.sqrt (4 * (312 : ℝ)) = 2 * Real.sqrt (312 : ℝ) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 2) (312 : ℝ),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    rwa [h2] at h1
  have hsT : 35 ≤ 312 := by norm_num
  have hsub : ((312 - 35 : ℕ) : ℝ) = (312 : ℝ) - (35 : ℝ) := by
    rw [Nat.cast_sub hsT]
    norm_num
  have hstep : (312 : ℝ) - 2 * Real.sqrt (312 : ℝ) ≤ ((312 - 35 : ℕ) : ℝ) := by
    rw [hsub]
    linarith [hfloor]
  have hsumI : (312 - 35) * 10 ^ 4 < ∑ p ∈ plist.filter (· ≤ 305), clbZ p := by
    rw [hplistLit1]
    decide
  have hsumR : ((312 - 35 : ℕ) : ℝ) <
      (∑ p ∈ plist.filter (· ≤ 305), (clbZ p : ℝ)) / 10 ^ 4 := by
    have h1 : ((312 - 35 : ℕ) : ℝ) * 10 ^ 4
        < ∑ p ∈ plist.filter (· ≤ 305), (clbZ p : ℝ) := by
      have h2 : ((312 - 35) * 10 ^ 4 : ℕ) < ∑ p ∈ plist.filter (· ≤ 305), clbZ p := hsumI
      exact_mod_cast h2
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
    exact h1
  calc (312 : ℝ) - 2 * Real.sqrt (312 : ℝ) ≤ ((312 - 35 : ℕ) : ℝ) := hstep
    _ < (∑ p ∈ plist.filter (· ≤ 305), (clbZ p : ℝ)) / 10 ^ 4 := hsumR
    _ ≤ ∑ p ∈ plist.filter (· ≤ 305), Real.log p := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
        calc (∑ p ∈ plist.filter (· ≤ 305), (clbZ p : ℝ))
            ≤ ∑ p ∈ plist.filter (· ≤ 305), Real.log p * 10 ^ 4 :=
              Finset.sum_le_sum (fun p hp => theta_cert_clbZ_le_log p (Finset.mem_of_mem_filter p hp))
          _ = (∑ p ∈ plist.filter (· ≤ 305), Real.log p) * 10 ^ 4 := by rw [Finset.sum_mul]
    _ = Chebyshev.theta ((305 : ℕ) : ℝ) := by
        rw [Chebyshev.theta_eq_sum_primesLE_log 305, theta_cert_primesLE_eq 305 (by norm_num)]

lemma blk_5 : ((324 : ℕ) : ℝ) - 2 * Real.sqrt ((324 : ℕ) : ℝ) < Chebyshev.theta ((312 : ℕ) : ℝ) := by
  have hfloor : (36 : ℝ) ≤ 2 * Real.sqrt (324 : ℝ) := by
    have h4 : (36 : ℝ) ^ 2 ≤ 4 * (324 : ℝ) := by norm_num
    have h1 := (Real.le_sqrt (by positivity : (0 : ℝ) ≤ (36 : ℝ))
      (by positivity : (0 : ℝ) ≤ 4 * (324 : ℝ))).mpr h4
    have h2 : Real.sqrt (4 * (324 : ℝ)) = 2 * Real.sqrt (324 : ℝ) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 2) (324 : ℝ),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    rwa [h2] at h1
  have hsT : 36 ≤ 324 := by norm_num
  have hsub : ((324 - 36 : ℕ) : ℝ) = (324 : ℝ) - (36 : ℝ) := by
    rw [Nat.cast_sub hsT]
    norm_num
  have hstep : (324 : ℝ) - 2 * Real.sqrt (324 : ℝ) ≤ ((324 - 36 : ℕ) : ℝ) := by
    rw [hsub]
    linarith [hfloor]
  have hsumI : (324 - 36) * 10 ^ 4 < ∑ p ∈ plist.filter (· ≤ 312), clbZ p := by
    rw [hplistLit1]
    decide
  have hsumR : ((324 - 36 : ℕ) : ℝ) <
      (∑ p ∈ plist.filter (· ≤ 312), (clbZ p : ℝ)) / 10 ^ 4 := by
    have h1 : ((324 - 36 : ℕ) : ℝ) * 10 ^ 4
        < ∑ p ∈ plist.filter (· ≤ 312), (clbZ p : ℝ) := by
      have h2 : ((324 - 36) * 10 ^ 4 : ℕ) < ∑ p ∈ plist.filter (· ≤ 312), clbZ p := hsumI
      exact_mod_cast h2
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
    exact h1
  calc (324 : ℝ) - 2 * Real.sqrt (324 : ℝ) ≤ ((324 - 36 : ℕ) : ℝ) := hstep
    _ < (∑ p ∈ plist.filter (· ≤ 312), (clbZ p : ℝ)) / 10 ^ 4 := hsumR
    _ ≤ ∑ p ∈ plist.filter (· ≤ 312), Real.log p := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
        calc (∑ p ∈ plist.filter (· ≤ 312), (clbZ p : ℝ))
            ≤ ∑ p ∈ plist.filter (· ≤ 312), Real.log p * 10 ^ 4 :=
              Finset.sum_le_sum (fun p hp => theta_cert_clbZ_le_log p (Finset.mem_of_mem_filter p hp))
          _ = (∑ p ∈ plist.filter (· ≤ 312), Real.log p) * 10 ^ 4 := by rw [Finset.sum_mul]
    _ = Chebyshev.theta ((312 : ℕ) : ℝ) := by
        rw [Chebyshev.theta_eq_sum_primesLE_log 312, theta_cert_primesLE_eq 312 (by norm_num)]

lemma blk_6 : ((335 : ℕ) : ℝ) - 2 * Real.sqrt ((335 : ℕ) : ℝ) < Chebyshev.theta ((324 : ℕ) : ℝ) := by
  have hfloor : (36 : ℝ) ≤ 2 * Real.sqrt (335 : ℝ) := by
    have h4 : (36 : ℝ) ^ 2 ≤ 4 * (335 : ℝ) := by norm_num
    have h1 := (Real.le_sqrt (by positivity : (0 : ℝ) ≤ (36 : ℝ))
      (by positivity : (0 : ℝ) ≤ 4 * (335 : ℝ))).mpr h4
    have h2 : Real.sqrt (4 * (335 : ℝ)) = 2 * Real.sqrt (335 : ℝ) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 2) (335 : ℝ),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    rwa [h2] at h1
  have hsT : 36 ≤ 335 := by norm_num
  have hsub : ((335 - 36 : ℕ) : ℝ) = (335 : ℝ) - (36 : ℝ) := by
    rw [Nat.cast_sub hsT]
    norm_num
  have hstep : (335 : ℝ) - 2 * Real.sqrt (335 : ℝ) ≤ ((335 - 36 : ℕ) : ℝ) := by
    rw [hsub]
    linarith [hfloor]
  have hsumI : (335 - 36) * 10 ^ 4 < ∑ p ∈ plist.filter (· ≤ 324), clbZ p := by
    rw [hplistLit1]
    decide
  have hsumR : ((335 - 36 : ℕ) : ℝ) <
      (∑ p ∈ plist.filter (· ≤ 324), (clbZ p : ℝ)) / 10 ^ 4 := by
    have h1 : ((335 - 36 : ℕ) : ℝ) * 10 ^ 4
        < ∑ p ∈ plist.filter (· ≤ 324), (clbZ p : ℝ) := by
      have h2 : ((335 - 36) * 10 ^ 4 : ℕ) < ∑ p ∈ plist.filter (· ≤ 324), clbZ p := hsumI
      exact_mod_cast h2
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
    exact h1
  calc (335 : ℝ) - 2 * Real.sqrt (335 : ℝ) ≤ ((335 - 36 : ℕ) : ℝ) := hstep
    _ < (∑ p ∈ plist.filter (· ≤ 324), (clbZ p : ℝ)) / 10 ^ 4 := hsumR
    _ ≤ ∑ p ∈ plist.filter (· ≤ 324), Real.log p := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
        calc (∑ p ∈ plist.filter (· ≤ 324), (clbZ p : ℝ))
            ≤ ∑ p ∈ plist.filter (· ≤ 324), Real.log p * 10 ^ 4 :=
              Finset.sum_le_sum (fun p hp => theta_cert_clbZ_le_log p (Finset.mem_of_mem_filter p hp))
          _ = (∑ p ∈ plist.filter (· ≤ 324), Real.log p) * 10 ^ 4 := by rw [Finset.sum_mul]
    _ = Chebyshev.theta ((324 : ℕ) : ℝ) := by
        rw [Chebyshev.theta_eq_sum_primesLE_log 324, theta_cert_primesLE_eq 324 (by norm_num)]

lemma blk_7 : ((341 : ℕ) : ℝ) - 2 * Real.sqrt ((341 : ℕ) : ℝ) < Chebyshev.theta ((335 : ℕ) : ℝ) := by
  have hfloor : (36 : ℝ) ≤ 2 * Real.sqrt (341 : ℝ) := by
    have h4 : (36 : ℝ) ^ 2 ≤ 4 * (341 : ℝ) := by norm_num
    have h1 := (Real.le_sqrt (by positivity : (0 : ℝ) ≤ (36 : ℝ))
      (by positivity : (0 : ℝ) ≤ 4 * (341 : ℝ))).mpr h4
    have h2 : Real.sqrt (4 * (341 : ℝ)) = 2 * Real.sqrt (341 : ℝ) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 2) (341 : ℝ),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    rwa [h2] at h1
  have hsT : 36 ≤ 341 := by norm_num
  have hsub : ((341 - 36 : ℕ) : ℝ) = (341 : ℝ) - (36 : ℝ) := by
    rw [Nat.cast_sub hsT]
    norm_num
  have hstep : (341 : ℝ) - 2 * Real.sqrt (341 : ℝ) ≤ ((341 - 36 : ℕ) : ℝ) := by
    rw [hsub]
    linarith [hfloor]
  have hsumI : (341 - 36) * 10 ^ 4 < ∑ p ∈ plist.filter (· ≤ 335), clbZ p := by
    rw [hplistLit1]
    decide
  have hsumR : ((341 - 36 : ℕ) : ℝ) <
      (∑ p ∈ plist.filter (· ≤ 335), (clbZ p : ℝ)) / 10 ^ 4 := by
    have h1 : ((341 - 36 : ℕ) : ℝ) * 10 ^ 4
        < ∑ p ∈ plist.filter (· ≤ 335), (clbZ p : ℝ) := by
      have h2 : ((341 - 36) * 10 ^ 4 : ℕ) < ∑ p ∈ plist.filter (· ≤ 335), clbZ p := hsumI
      exact_mod_cast h2
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
    exact h1
  calc (341 : ℝ) - 2 * Real.sqrt (341 : ℝ) ≤ ((341 - 36 : ℕ) : ℝ) := hstep
    _ < (∑ p ∈ plist.filter (· ≤ 335), (clbZ p : ℝ)) / 10 ^ 4 := hsumR
    _ ≤ ∑ p ∈ plist.filter (· ≤ 335), Real.log p := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
        calc (∑ p ∈ plist.filter (· ≤ 335), (clbZ p : ℝ))
            ≤ ∑ p ∈ plist.filter (· ≤ 335), Real.log p * 10 ^ 4 :=
              Finset.sum_le_sum (fun p hp => theta_cert_clbZ_le_log p (Finset.mem_of_mem_filter p hp))
          _ = (∑ p ∈ plist.filter (· ≤ 335), Real.log p) * 10 ^ 4 := by rw [Finset.sum_mul]
    _ = Chebyshev.theta ((335 : ℕ) : ℝ) := by
        rw [Chebyshev.theta_eq_sum_primesLE_log 335, theta_cert_primesLE_eq 335 (by norm_num)]

lemma blk_8 : ((348 : ℕ) : ℝ) - 2 * Real.sqrt ((348 : ℕ) : ℝ) < Chebyshev.theta ((341 : ℕ) : ℝ) := by
  have hfloor : (37 : ℝ) ≤ 2 * Real.sqrt (348 : ℝ) := by
    have h4 : (37 : ℝ) ^ 2 ≤ 4 * (348 : ℝ) := by norm_num
    have h1 := (Real.le_sqrt (by positivity : (0 : ℝ) ≤ (37 : ℝ))
      (by positivity : (0 : ℝ) ≤ 4 * (348 : ℝ))).mpr h4
    have h2 : Real.sqrt (4 * (348 : ℝ)) = 2 * Real.sqrt (348 : ℝ) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 2) (348 : ℝ),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    rwa [h2] at h1
  have hsT : 37 ≤ 348 := by norm_num
  have hsub : ((348 - 37 : ℕ) : ℝ) = (348 : ℝ) - (37 : ℝ) := by
    rw [Nat.cast_sub hsT]
    norm_num
  have hstep : (348 : ℝ) - 2 * Real.sqrt (348 : ℝ) ≤ ((348 - 37 : ℕ) : ℝ) := by
    rw [hsub]
    linarith [hfloor]
  have hsumI : (348 - 37) * 10 ^ 4 < ∑ p ∈ plist.filter (· ≤ 341), clbZ p := by
    rw [hplistLit1]
    decide
  have hsumR : ((348 - 37 : ℕ) : ℝ) <
      (∑ p ∈ plist.filter (· ≤ 341), (clbZ p : ℝ)) / 10 ^ 4 := by
    have h1 : ((348 - 37 : ℕ) : ℝ) * 10 ^ 4
        < ∑ p ∈ plist.filter (· ≤ 341), (clbZ p : ℝ) := by
      have h2 : ((348 - 37) * 10 ^ 4 : ℕ) < ∑ p ∈ plist.filter (· ≤ 341), clbZ p := hsumI
      exact_mod_cast h2
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
    exact h1
  calc (348 : ℝ) - 2 * Real.sqrt (348 : ℝ) ≤ ((348 - 37 : ℕ) : ℝ) := hstep
    _ < (∑ p ∈ plist.filter (· ≤ 341), (clbZ p : ℝ)) / 10 ^ 4 := hsumR
    _ ≤ ∑ p ∈ plist.filter (· ≤ 341), Real.log p := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
        calc (∑ p ∈ plist.filter (· ≤ 341), (clbZ p : ℝ))
            ≤ ∑ p ∈ plist.filter (· ≤ 341), Real.log p * 10 ^ 4 :=
              Finset.sum_le_sum (fun p hp => theta_cert_clbZ_le_log p (Finset.mem_of_mem_filter p hp))
          _ = (∑ p ∈ plist.filter (· ≤ 341), Real.log p) * 10 ^ 4 := by rw [Finset.sum_mul]
    _ = Chebyshev.theta ((341 : ℕ) : ℝ) := by
        rw [Chebyshev.theta_eq_sum_primesLE_log 341, theta_cert_primesLE_eq 341 (by norm_num)]

lemma blk_9 : ((354 : ℕ) : ℝ) - 2 * Real.sqrt ((354 : ℕ) : ℝ) < Chebyshev.theta ((348 : ℕ) : ℝ) := by
  have hfloor : (37 : ℝ) ≤ 2 * Real.sqrt (354 : ℝ) := by
    have h4 : (37 : ℝ) ^ 2 ≤ 4 * (354 : ℝ) := by norm_num
    have h1 := (Real.le_sqrt (by positivity : (0 : ℝ) ≤ (37 : ℝ))
      (by positivity : (0 : ℝ) ≤ 4 * (354 : ℝ))).mpr h4
    have h2 : Real.sqrt (4 * (354 : ℝ)) = 2 * Real.sqrt (354 : ℝ) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 2) (354 : ℝ),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    rwa [h2] at h1
  have hsT : 37 ≤ 354 := by norm_num
  have hsub : ((354 - 37 : ℕ) : ℝ) = (354 : ℝ) - (37 : ℝ) := by
    rw [Nat.cast_sub hsT]
    norm_num
  have hstep : (354 : ℝ) - 2 * Real.sqrt (354 : ℝ) ≤ ((354 - 37 : ℕ) : ℝ) := by
    rw [hsub]
    linarith [hfloor]
  have hsumI : (354 - 37) * 10 ^ 4 < ∑ p ∈ plist.filter (· ≤ 348), clbZ p := by
    rw [hplistLit1]
    decide
  have hsumR : ((354 - 37 : ℕ) : ℝ) <
      (∑ p ∈ plist.filter (· ≤ 348), (clbZ p : ℝ)) / 10 ^ 4 := by
    have h1 : ((354 - 37 : ℕ) : ℝ) * 10 ^ 4
        < ∑ p ∈ plist.filter (· ≤ 348), (clbZ p : ℝ) := by
      have h2 : ((354 - 37) * 10 ^ 4 : ℕ) < ∑ p ∈ plist.filter (· ≤ 348), clbZ p := hsumI
      exact_mod_cast h2
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
    exact h1
  calc (354 : ℝ) - 2 * Real.sqrt (354 : ℝ) ≤ ((354 - 37 : ℕ) : ℝ) := hstep
    _ < (∑ p ∈ plist.filter (· ≤ 348), (clbZ p : ℝ)) / 10 ^ 4 := hsumR
    _ ≤ ∑ p ∈ plist.filter (· ≤ 348), Real.log p := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
        calc (∑ p ∈ plist.filter (· ≤ 348), (clbZ p : ℝ))
            ≤ ∑ p ∈ plist.filter (· ≤ 348), Real.log p * 10 ^ 4 :=
              Finset.sum_le_sum (fun p hp => theta_cert_clbZ_le_log p (Finset.mem_of_mem_filter p hp))
          _ = (∑ p ∈ plist.filter (· ≤ 348), Real.log p) * 10 ^ 4 := by rw [Finset.sum_mul]
    _ = Chebyshev.theta ((348 : ℕ) : ℝ) := by
        rw [Chebyshev.theta_eq_sum_primesLE_log 348, theta_cert_primesLE_eq 348 (by norm_num)]

lemma blk_10 : ((367 : ℕ) : ℝ) - 2 * Real.sqrt ((367 : ℕ) : ℝ) < Chebyshev.theta ((354 : ℕ) : ℝ) := by
  have hfloor : (38 : ℝ) ≤ 2 * Real.sqrt (367 : ℝ) := by
    have h4 : (38 : ℝ) ^ 2 ≤ 4 * (367 : ℝ) := by norm_num
    have h1 := (Real.le_sqrt (by positivity : (0 : ℝ) ≤ (38 : ℝ))
      (by positivity : (0 : ℝ) ≤ 4 * (367 : ℝ))).mpr h4
    have h2 : Real.sqrt (4 * (367 : ℝ)) = 2 * Real.sqrt (367 : ℝ) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 2) (367 : ℝ),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    rwa [h2] at h1
  have hsT : 38 ≤ 367 := by norm_num
  have hsub : ((367 - 38 : ℕ) : ℝ) = (367 : ℝ) - (38 : ℝ) := by
    rw [Nat.cast_sub hsT]
    norm_num
  have hstep : (367 : ℝ) - 2 * Real.sqrt (367 : ℝ) ≤ ((367 - 38 : ℕ) : ℝ) := by
    rw [hsub]
    linarith [hfloor]
  have hsumI : (367 - 38) * 10 ^ 4 < ∑ p ∈ plist.filter (· ≤ 354), clbZ p := by
    rw [hplistLit1]
    decide
  have hsumR : ((367 - 38 : ℕ) : ℝ) <
      (∑ p ∈ plist.filter (· ≤ 354), (clbZ p : ℝ)) / 10 ^ 4 := by
    have h1 : ((367 - 38 : ℕ) : ℝ) * 10 ^ 4
        < ∑ p ∈ plist.filter (· ≤ 354), (clbZ p : ℝ) := by
      have h2 : ((367 - 38) * 10 ^ 4 : ℕ) < ∑ p ∈ plist.filter (· ≤ 354), clbZ p := hsumI
      exact_mod_cast h2
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
    exact h1
  calc (367 : ℝ) - 2 * Real.sqrt (367 : ℝ) ≤ ((367 - 38 : ℕ) : ℝ) := hstep
    _ < (∑ p ∈ plist.filter (· ≤ 354), (clbZ p : ℝ)) / 10 ^ 4 := hsumR
    _ ≤ ∑ p ∈ plist.filter (· ≤ 354), Real.log p := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
        calc (∑ p ∈ plist.filter (· ≤ 354), (clbZ p : ℝ))
            ≤ ∑ p ∈ plist.filter (· ≤ 354), Real.log p * 10 ^ 4 :=
              Finset.sum_le_sum (fun p hp => theta_cert_clbZ_le_log p (Finset.mem_of_mem_filter p hp))
          _ = (∑ p ∈ plist.filter (· ≤ 354), Real.log p) * 10 ^ 4 := by rw [Finset.sum_mul]
    _ = Chebyshev.theta ((354 : ℕ) : ℝ) := by
        rw [Chebyshev.theta_eq_sum_primesLE_log 354, theta_cert_primesLE_eq 354 (by norm_num)]

lemma blk_11 : ((378 : ℕ) : ℝ) - 2 * Real.sqrt ((378 : ℕ) : ℝ) < Chebyshev.theta ((367 : ℕ) : ℝ) := by
  have hfloor : (38 : ℝ) ≤ 2 * Real.sqrt (378 : ℝ) := by
    have h4 : (38 : ℝ) ^ 2 ≤ 4 * (378 : ℝ) := by norm_num
    have h1 := (Real.le_sqrt (by positivity : (0 : ℝ) ≤ (38 : ℝ))
      (by positivity : (0 : ℝ) ≤ 4 * (378 : ℝ))).mpr h4
    have h2 : Real.sqrt (4 * (378 : ℝ)) = 2 * Real.sqrt (378 : ℝ) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 2) (378 : ℝ),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    rwa [h2] at h1
  have hsT : 38 ≤ 378 := by norm_num
  have hsub : ((378 - 38 : ℕ) : ℝ) = (378 : ℝ) - (38 : ℝ) := by
    rw [Nat.cast_sub hsT]
    norm_num
  have hstep : (378 : ℝ) - 2 * Real.sqrt (378 : ℝ) ≤ ((378 - 38 : ℕ) : ℝ) := by
    rw [hsub]
    linarith [hfloor]
  have hsumI : (378 - 38) * 10 ^ 4 < ∑ p ∈ plist.filter (· ≤ 367), clbZ p := by
    rw [hplistLit1]
    decide
  have hsumR : ((378 - 38 : ℕ) : ℝ) <
      (∑ p ∈ plist.filter (· ≤ 367), (clbZ p : ℝ)) / 10 ^ 4 := by
    have h1 : ((378 - 38 : ℕ) : ℝ) * 10 ^ 4
        < ∑ p ∈ plist.filter (· ≤ 367), (clbZ p : ℝ) := by
      have h2 : ((378 - 38) * 10 ^ 4 : ℕ) < ∑ p ∈ plist.filter (· ≤ 367), clbZ p := hsumI
      exact_mod_cast h2
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
    exact h1
  calc (378 : ℝ) - 2 * Real.sqrt (378 : ℝ) ≤ ((378 - 38 : ℕ) : ℝ) := hstep
    _ < (∑ p ∈ plist.filter (· ≤ 367), (clbZ p : ℝ)) / 10 ^ 4 := hsumR
    _ ≤ ∑ p ∈ plist.filter (· ≤ 367), Real.log p := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
        calc (∑ p ∈ plist.filter (· ≤ 367), (clbZ p : ℝ))
            ≤ ∑ p ∈ plist.filter (· ≤ 367), Real.log p * 10 ^ 4 :=
              Finset.sum_le_sum (fun p hp => theta_cert_clbZ_le_log p (Finset.mem_of_mem_filter p hp))
          _ = (∑ p ∈ plist.filter (· ≤ 367), Real.log p) * 10 ^ 4 := by rw [Finset.sum_mul]
    _ = Chebyshev.theta ((367 : ℕ) : ℝ) := by
        rw [Chebyshev.theta_eq_sum_primesLE_log 367, theta_cert_primesLE_eq 367 (by norm_num)]

lemma blk_12 : ((385 : ℕ) : ℝ) - 2 * Real.sqrt ((385 : ℕ) : ℝ) < Chebyshev.theta ((378 : ℕ) : ℝ) := by
  have hfloor : (39 : ℝ) ≤ 2 * Real.sqrt (385 : ℝ) := by
    have h4 : (39 : ℝ) ^ 2 ≤ 4 * (385 : ℝ) := by norm_num
    have h1 := (Real.le_sqrt (by positivity : (0 : ℝ) ≤ (39 : ℝ))
      (by positivity : (0 : ℝ) ≤ 4 * (385 : ℝ))).mpr h4
    have h2 : Real.sqrt (4 * (385 : ℝ)) = 2 * Real.sqrt (385 : ℝ) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 2) (385 : ℝ),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    rwa [h2] at h1
  have hsT : 39 ≤ 385 := by norm_num
  have hsub : ((385 - 39 : ℕ) : ℝ) = (385 : ℝ) - (39 : ℝ) := by
    rw [Nat.cast_sub hsT]
    norm_num
  have hstep : (385 : ℝ) - 2 * Real.sqrt (385 : ℝ) ≤ ((385 - 39 : ℕ) : ℝ) := by
    rw [hsub]
    linarith [hfloor]
  have hsumI : (385 - 39) * 10 ^ 4 < ∑ p ∈ plist.filter (· ≤ 378), clbZ p := by
    rw [hplistLit1]
    decide
  have hsumR : ((385 - 39 : ℕ) : ℝ) <
      (∑ p ∈ plist.filter (· ≤ 378), (clbZ p : ℝ)) / 10 ^ 4 := by
    have h1 : ((385 - 39 : ℕ) : ℝ) * 10 ^ 4
        < ∑ p ∈ plist.filter (· ≤ 378), (clbZ p : ℝ) := by
      have h2 : ((385 - 39) * 10 ^ 4 : ℕ) < ∑ p ∈ plist.filter (· ≤ 378), clbZ p := hsumI
      exact_mod_cast h2
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
    exact h1
  calc (385 : ℝ) - 2 * Real.sqrt (385 : ℝ) ≤ ((385 - 39 : ℕ) : ℝ) := hstep
    _ < (∑ p ∈ plist.filter (· ≤ 378), (clbZ p : ℝ)) / 10 ^ 4 := hsumR
    _ ≤ ∑ p ∈ plist.filter (· ≤ 378), Real.log p := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
        calc (∑ p ∈ plist.filter (· ≤ 378), (clbZ p : ℝ))
            ≤ ∑ p ∈ plist.filter (· ≤ 378), Real.log p * 10 ^ 4 :=
              Finset.sum_le_sum (fun p hp => theta_cert_clbZ_le_log p (Finset.mem_of_mem_filter p hp))
          _ = (∑ p ∈ plist.filter (· ≤ 378), Real.log p) * 10 ^ 4 := by rw [Finset.sum_mul]
    _ = Chebyshev.theta ((378 : ℕ) : ℝ) := by
        rw [Chebyshev.theta_eq_sum_primesLE_log 378, theta_cert_primesLE_eq 378 (by norm_num)]

lemma blk_13 : ((397 : ℕ) : ℝ) - 2 * Real.sqrt ((397 : ℕ) : ℝ) < Chebyshev.theta ((385 : ℕ) : ℝ) := by
  have hfloor : (39 : ℝ) ≤ 2 * Real.sqrt (397 : ℝ) := by
    have h4 : (39 : ℝ) ^ 2 ≤ 4 * (397 : ℝ) := by norm_num
    have h1 := (Real.le_sqrt (by positivity : (0 : ℝ) ≤ (39 : ℝ))
      (by positivity : (0 : ℝ) ≤ 4 * (397 : ℝ))).mpr h4
    have h2 : Real.sqrt (4 * (397 : ℝ)) = 2 * Real.sqrt (397 : ℝ) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 2) (397 : ℝ),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    rwa [h2] at h1
  have hsT : 39 ≤ 397 := by norm_num
  have hsub : ((397 - 39 : ℕ) : ℝ) = (397 : ℝ) - (39 : ℝ) := by
    rw [Nat.cast_sub hsT]
    norm_num
  have hstep : (397 : ℝ) - 2 * Real.sqrt (397 : ℝ) ≤ ((397 - 39 : ℕ) : ℝ) := by
    rw [hsub]
    linarith [hfloor]
  have hsumI : (397 - 39) * 10 ^ 4 < ∑ p ∈ plist.filter (· ≤ 385), clbZ p := by
    rw [hplistLit1]
    decide
  have hsumR : ((397 - 39 : ℕ) : ℝ) <
      (∑ p ∈ plist.filter (· ≤ 385), (clbZ p : ℝ)) / 10 ^ 4 := by
    have h1 : ((397 - 39 : ℕ) : ℝ) * 10 ^ 4
        < ∑ p ∈ plist.filter (· ≤ 385), (clbZ p : ℝ) := by
      have h2 : ((397 - 39) * 10 ^ 4 : ℕ) < ∑ p ∈ plist.filter (· ≤ 385), clbZ p := hsumI
      exact_mod_cast h2
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
    exact h1
  calc (397 : ℝ) - 2 * Real.sqrt (397 : ℝ) ≤ ((397 - 39 : ℕ) : ℝ) := hstep
    _ < (∑ p ∈ plist.filter (· ≤ 385), (clbZ p : ℝ)) / 10 ^ 4 := hsumR
    _ ≤ ∑ p ∈ plist.filter (· ≤ 385), Real.log p := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
        calc (∑ p ∈ plist.filter (· ≤ 385), (clbZ p : ℝ))
            ≤ ∑ p ∈ plist.filter (· ≤ 385), Real.log p * 10 ^ 4 :=
              Finset.sum_le_sum (fun p hp => theta_cert_clbZ_le_log p (Finset.mem_of_mem_filter p hp))
          _ = (∑ p ∈ plist.filter (· ≤ 385), Real.log p) * 10 ^ 4 := by rw [Finset.sum_mul]
    _ = Chebyshev.theta ((385 : ℕ) : ℝ) := by
        rw [Chebyshev.theta_eq_sum_primesLE_log 385, theta_cert_primesLE_eq 385 (by norm_num)]

lemma blk_14 : ((410 : ℕ) : ℝ) - 2 * Real.sqrt ((410 : ℕ) : ℝ) < Chebyshev.theta ((397 : ℕ) : ℝ) := by
  have hfloor : (40 : ℝ) ≤ 2 * Real.sqrt (410 : ℝ) := by
    have h4 : (40 : ℝ) ^ 2 ≤ 4 * (410 : ℝ) := by norm_num
    have h1 := (Real.le_sqrt (by positivity : (0 : ℝ) ≤ (40 : ℝ))
      (by positivity : (0 : ℝ) ≤ 4 * (410 : ℝ))).mpr h4
    have h2 : Real.sqrt (4 * (410 : ℝ)) = 2 * Real.sqrt (410 : ℝ) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 2) (410 : ℝ),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    rwa [h2] at h1
  have hsT : 40 ≤ 410 := by norm_num
  have hsub : ((410 - 40 : ℕ) : ℝ) = (410 : ℝ) - (40 : ℝ) := by
    rw [Nat.cast_sub hsT]
    norm_num
  have hstep : (410 : ℝ) - 2 * Real.sqrt (410 : ℝ) ≤ ((410 - 40 : ℕ) : ℝ) := by
    rw [hsub]
    linarith [hfloor]
  have hsumI : (410 - 40) * 10 ^ 4 < ∑ p ∈ plist.filter (· ≤ 397), clbZ p := by
    rw [hplistLit1]
    decide
  have hsumR : ((410 - 40 : ℕ) : ℝ) <
      (∑ p ∈ plist.filter (· ≤ 397), (clbZ p : ℝ)) / 10 ^ 4 := by
    have h1 : ((410 - 40 : ℕ) : ℝ) * 10 ^ 4
        < ∑ p ∈ plist.filter (· ≤ 397), (clbZ p : ℝ) := by
      have h2 : ((410 - 40) * 10 ^ 4 : ℕ) < ∑ p ∈ plist.filter (· ≤ 397), clbZ p := hsumI
      exact_mod_cast h2
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
    exact h1
  calc (410 : ℝ) - 2 * Real.sqrt (410 : ℝ) ≤ ((410 - 40 : ℕ) : ℝ) := hstep
    _ < (∑ p ∈ plist.filter (· ≤ 397), (clbZ p : ℝ)) / 10 ^ 4 := hsumR
    _ ≤ ∑ p ∈ plist.filter (· ≤ 397), Real.log p := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
        calc (∑ p ∈ plist.filter (· ≤ 397), (clbZ p : ℝ))
            ≤ ∑ p ∈ plist.filter (· ≤ 397), Real.log p * 10 ^ 4 :=
              Finset.sum_le_sum (fun p hp => theta_cert_clbZ_le_log p (Finset.mem_of_mem_filter p hp))
          _ = (∑ p ∈ plist.filter (· ≤ 397), Real.log p) * 10 ^ 4 := by rw [Finset.sum_mul]
    _ = Chebyshev.theta ((397 : ℕ) : ℝ) := by
        rw [Chebyshev.theta_eq_sum_primesLE_log 397, theta_cert_primesLE_eq 397 (by norm_num)]

lemma blk_15 : ((423 : ℕ) : ℝ) - 2 * Real.sqrt ((423 : ℕ) : ℝ) < Chebyshev.theta ((410 : ℕ) : ℝ) := by
  have hfloor : (41 : ℝ) ≤ 2 * Real.sqrt (423 : ℝ) := by
    have h4 : (41 : ℝ) ^ 2 ≤ 4 * (423 : ℝ) := by norm_num
    have h1 := (Real.le_sqrt (by positivity : (0 : ℝ) ≤ (41 : ℝ))
      (by positivity : (0 : ℝ) ≤ 4 * (423 : ℝ))).mpr h4
    have h2 : Real.sqrt (4 * (423 : ℝ)) = 2 * Real.sqrt (423 : ℝ) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 2) (423 : ℝ),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    rwa [h2] at h1
  have hsT : 41 ≤ 423 := by norm_num
  have hsub : ((423 - 41 : ℕ) : ℝ) = (423 : ℝ) - (41 : ℝ) := by
    rw [Nat.cast_sub hsT]
    norm_num
  have hstep : (423 : ℝ) - 2 * Real.sqrt (423 : ℝ) ≤ ((423 - 41 : ℕ) : ℝ) := by
    rw [hsub]
    linarith [hfloor]
  have hsumI : (423 - 41) * 10 ^ 4 < ∑ p ∈ plist.filter (· ≤ 410), clbZ p := by
    rw [hplistLit1]
    decide
  have hsumR : ((423 - 41 : ℕ) : ℝ) <
      (∑ p ∈ plist.filter (· ≤ 410), (clbZ p : ℝ)) / 10 ^ 4 := by
    have h1 : ((423 - 41 : ℕ) : ℝ) * 10 ^ 4
        < ∑ p ∈ plist.filter (· ≤ 410), (clbZ p : ℝ) := by
      have h2 : ((423 - 41) * 10 ^ 4 : ℕ) < ∑ p ∈ plist.filter (· ≤ 410), clbZ p := hsumI
      exact_mod_cast h2
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
    exact h1
  calc (423 : ℝ) - 2 * Real.sqrt (423 : ℝ) ≤ ((423 - 41 : ℕ) : ℝ) := hstep
    _ < (∑ p ∈ plist.filter (· ≤ 410), (clbZ p : ℝ)) / 10 ^ 4 := hsumR
    _ ≤ ∑ p ∈ plist.filter (· ≤ 410), Real.log p := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
        calc (∑ p ∈ plist.filter (· ≤ 410), (clbZ p : ℝ))
            ≤ ∑ p ∈ plist.filter (· ≤ 410), Real.log p * 10 ^ 4 :=
              Finset.sum_le_sum (fun p hp => theta_cert_clbZ_le_log p (Finset.mem_of_mem_filter p hp))
          _ = (∑ p ∈ plist.filter (· ≤ 410), Real.log p) * 10 ^ 4 := by rw [Finset.sum_mul]
    _ = Chebyshev.theta ((410 : ℕ) : ℝ) := by
        rw [Chebyshev.theta_eq_sum_primesLE_log 410, theta_cert_primesLE_eq 410 (by norm_num)]

lemma blk_16 : ((435 : ℕ) : ℝ) - 2 * Real.sqrt ((435 : ℕ) : ℝ) < Chebyshev.theta ((423 : ℕ) : ℝ) := by
  have hfloor : (41 : ℝ) ≤ 2 * Real.sqrt (435 : ℝ) := by
    have h4 : (41 : ℝ) ^ 2 ≤ 4 * (435 : ℝ) := by norm_num
    have h1 := (Real.le_sqrt (by positivity : (0 : ℝ) ≤ (41 : ℝ))
      (by positivity : (0 : ℝ) ≤ 4 * (435 : ℝ))).mpr h4
    have h2 : Real.sqrt (4 * (435 : ℝ)) = 2 * Real.sqrt (435 : ℝ) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 2) (435 : ℝ),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    rwa [h2] at h1
  have hsT : 41 ≤ 435 := by norm_num
  have hsub : ((435 - 41 : ℕ) : ℝ) = (435 : ℝ) - (41 : ℝ) := by
    rw [Nat.cast_sub hsT]
    norm_num
  have hstep : (435 : ℝ) - 2 * Real.sqrt (435 : ℝ) ≤ ((435 - 41 : ℕ) : ℝ) := by
    rw [hsub]
    linarith [hfloor]
  have hsumI : (435 - 41) * 10 ^ 4 < ∑ p ∈ plist.filter (· ≤ 423), clbZ p := by
    rw [hplistLit1]
    decide
  have hsumR : ((435 - 41 : ℕ) : ℝ) <
      (∑ p ∈ plist.filter (· ≤ 423), (clbZ p : ℝ)) / 10 ^ 4 := by
    have h1 : ((435 - 41 : ℕ) : ℝ) * 10 ^ 4
        < ∑ p ∈ plist.filter (· ≤ 423), (clbZ p : ℝ) := by
      have h2 : ((435 - 41) * 10 ^ 4 : ℕ) < ∑ p ∈ plist.filter (· ≤ 423), clbZ p := hsumI
      exact_mod_cast h2
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
    exact h1
  calc (435 : ℝ) - 2 * Real.sqrt (435 : ℝ) ≤ ((435 - 41 : ℕ) : ℝ) := hstep
    _ < (∑ p ∈ plist.filter (· ≤ 423), (clbZ p : ℝ)) / 10 ^ 4 := hsumR
    _ ≤ ∑ p ∈ plist.filter (· ≤ 423), Real.log p := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 4)]
        calc (∑ p ∈ plist.filter (· ≤ 423), (clbZ p : ℝ))
            ≤ ∑ p ∈ plist.filter (· ≤ 423), Real.log p * 10 ^ 4 :=
              Finset.sum_le_sum (fun p hp => theta_cert_clbZ_le_log p (Finset.mem_of_mem_filter p hp))
          _ = (∑ p ∈ plist.filter (· ≤ 423), Real.log p) * 10 ^ 4 := by rw [Finset.sum_mul]
    _ = Chebyshev.theta ((423 : ℕ) : ℝ) := by
        rw [Chebyshev.theta_eq_sum_primesLE_log 423, theta_cert_primesLE_eq 423 (by norm_num)]


theorem solution (ab : ℕ × ℕ) (hab : ab ∈ blk1) :
    ((min (ab.2 + 1) 1420 : ℕ) : ℝ) - 2 * Real.sqrt ((min (ab.2 + 1) 1420 : ℕ) : ℝ) <
      Chebyshev.theta ((ab.1 : ℕ) : ℝ) := by
  have hmem := hab
  simp only [blk1, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals cases h
  all_goals (first | exact blk_0 | exact blk_1 | exact blk_2 | exact blk_3 | exact blk_4 | exact blk_5 | exact blk_6 | exact blk_7 | exact blk_8 | exact blk_9 | exact blk_10 | exact blk_11 | exact blk_12 | exact blk_13 | exact blk_14 | exact blk_15 | exact blk_16)

end TaoFivePrimes


open TaoFivePrimes

/-- The verification harness looks for `theorem solution` in the root
namespace, so the namespaced proof above is re-exported at the root. -/
theorem solution (ab : ℕ × ℕ) (hab : ab ∈ blk1) :
    ((min (ab.2 + 1) 1420 : ℕ) : ℝ) - 2 * Real.sqrt ((min (ab.2 + 1) 1420 : ℕ) : ℝ) <
      Chebyshev.theta ((ab.1 : ℕ) : ℝ) :=
  TaoFivePrimes.solution ab hab
