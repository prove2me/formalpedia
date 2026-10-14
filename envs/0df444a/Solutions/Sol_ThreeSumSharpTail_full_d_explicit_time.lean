-- Prove2me | solution 1 for ThreeSumSharpTail.full_d_explicit_time
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-13T19:29:56.229989+00:00
-- url     : https://prove2.me/submissions/fb5f8d00-c360-4baf-b18b-4678342b5700

import Definitions.Def_APSP299791_Defs4
import Theorems.Thm_ThreeSumSharpTail_full_d_call_total
import Theorems.Thm_ThreeSumSharpTail_full_d_extra_total
import Mathlib

open ThreeSumApsp Filter

/-- Generic full-D Theorem 17 gives the sharp saving, retaining the logarithmic factors. -/
theorem solution (M : DetTimeModel) (a s : ℝ) (D g : ℕ → ℕ)
    (ha0 : 0 < a) (ha1 : a ≤ 1) (hs0 : 0 ≤ s) (hsHalf : s ≤ 1 / 2)
    (hDfloor : ∀ n, D n = ⌊(n : ℝ) ^ a⌋₊)
    (hgceil : ∀ n, 1 ≤ D n → g n = ⌈(D n : ℝ) ^ (s / 2)⌉₊)
    (hprime : Real.logb 2 7 + 3 * a / 2 ≤ 3 - a * s / 2)
    (hbuild : a * (1 + s) ≤ 1)
    (h17 : Claim.Theorem_17 M strassen D g)
    (hlop : ∃ (C : ℝ) (Td : ℕ → ℕ → ℕ → ℝ), 0 ≤ C ∧ M.lopDetect Td ∧
      ∀ n d w : ℕ, 1 ≤ d → (d : ℝ) ≤ (n : ℝ) ^ a →
        Td n d w ≤ C * ((n : ℝ) ^ 2 * (Real.log d + 1) ^ 2 / (d : ℝ) ^ s +
          (w : ℝ) * (d : ℝ) ^ (1 / 2 - s) * (Real.log d + 1) + (n : ℝ) * d + w + 1)) :
    ∃ n₀, Claim.Theorem_19_explicitAt M (a * s / 2) 2 n₀ := by
  obtain ⟨C', hC', h17⟩ := h17
  obtain ⟨C, Td, hC, hTd, hlop⟩ := hlop
  obtain ⟨T, hT, h17⟩ := h17 Td hTd
  have hlarge : ∀ᶠ n : ℕ in atTop, 3 ≤ n ∧ (17 : ℝ) ≤ (n : ℝ) ^ a := by
    have hp := (tendsto_rpow_atTop ha0).comp (tendsto_natCast_atTop_atTop (R := ℝ))
    filter_upwards [eventually_ge_atTop 3, hp.eventually_ge_atTop 17] with n hn hp
    exact ⟨hn, hp⟩
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hlarge
  refine ⟨n₀, 2 * (256 * C + 36 * C'), T, hT, fun n κ u hn hκ hu => ?_⟩
  obtain ⟨hn3, hroot17⟩ := hn₀ n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn0 : (0 : ℝ) < n := zero_lt_one.trans_le hn1
  have hDle : (D n : ℝ) ≤ (n : ℝ) ^ a := by rw [hDfloor]; exact Nat.floor_le (by positivity)
  have hDlt : (n : ℝ) ^ a < (D n : ℝ) + 1 := by rw [hDfloor]; exact Nat.lt_floor_add_one _
  have hD16 : 16 ≤ D n := by
    have h : (16 : ℝ) ≤ D n := by linarith
    exact_mod_cast h
  have hD1 : 1 ≤ D n := by omega
  have hD1r : (1 : ℝ) ≤ D n := by exact_mod_cast hD1
  have hD0 : (0 : ℝ) < D n := zero_lt_one.trans_le hD1r
  have hDnR : (D n : ℝ) ≤ n := by
    calc
      (D n : ℝ) ≤ (n : ℝ) ^ a := hDle
      _ ≤ (n : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hn1 ha1
      _ = n := Real.rpow_one _
  have hDn : D n ≤ n := by exact_mod_cast hDnR
  have hgp1 : (1 : ℝ) ≤ (D n : ℝ) ^ (s / 2) := Real.one_le_rpow hD1r (by positivity)
  have hgLo : (D n : ℝ) ^ (s / 2) ≤ g n := by rw [hgceil n hD1]; exact Nat.le_ceil _
  have hg1 : 1 ≤ g n := by exact_mod_cast hgp1.trans hgLo
  have hgHi : (g n : ℝ) ≤ 2 * (D n : ℝ) ^ (s / 2) := by
    have h : (g n : ℝ) < (D n : ℝ) ^ (s / 2) + 1 := by
      rw [hgceil n hD1]
      exact Nat.ceil_lt_add_one (by positivity)
    linarith
  have hgsqrt : (g n : ℝ) ≤ Real.sqrt (D n) := by
    have htwo : (2 : ℝ) ≤ (D n : ℝ) ^ (1 / 4 : ℝ) := by
      calc
        (2 : ℝ) = (16 : ℝ) ^ (1 / 4 : ℝ) := by
          rw [show (16 : ℝ) = 2 ^ (4 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
          norm_num
        _ ≤ (D n : ℝ) ^ (1 / 4 : ℝ) :=
          Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hD16) (by norm_num)
    calc
      (g n : ℝ) ≤ 2 * (D n : ℝ) ^ (s / 2) := hgHi
      _ ≤ (D n : ℝ) ^ (1 / 4 : ℝ) * (D n : ℝ) ^ (1 / 4 : ℝ) := by
        apply mul_le_mul htwo
          (Real.rpow_le_rpow_of_exponent_le hD1r (by linarith)) (by positivity) (by positivity)
      _ = Real.sqrt (D n) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add hD0]
        norm_num
  have hfit : (D n : ℝ) ^ (1 + s) ≤ n := by
    calc
      (D n : ℝ) ^ (1 + s) ≤ ((n : ℝ) ^ a) ^ (1 + s) :=
        Real.rpow_le_rpow hD0.le hDle (by linarith)
      _ = (n : ℝ) ^ (a * (1 + s)) := by rw [Real.rpow_mul hn0.le]
      _ ≤ (n : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hn1 hbuild
      _ = n := Real.rpow_one _
  have hlog : 1 ≤ Real.log n := Real.one_le_log_natCast_of_three_le hn3
  have hlogD0 : 0 ≤ Real.log (D n) := Real.log_nonneg hD1r
  have hlogD : Real.log (D n) + 1 ≤ 2 * Real.log n := by
    have := Real.log_le_log hD0 hDnR
    linarith
  have hlogSq : (Real.log (D n) + 1) ^ 2 ≤ 4 * Real.log n ^ 2 := by
    have h := pow_le_pow_left₀ (by linarith : 0 ≤ Real.log (D n) + 1) hlogD 2
    nlinarith
  set S := (n : ℝ) ^ 3 * (D n : ℝ) ^ (-s / 2) with hS
  set X := κ * (S * Real.log n ^ 2) with hX
  have hS0 : 0 ≤ S := by positivity
  have hSL2X : S * Real.log n ^ 2 ≤ X := by
    rw [hX]
    simpa only [one_mul] using
      (mul_le_mul_of_nonneg_right hκ (mul_nonneg hS0 (sq_nonneg (Real.log n))))
  have hcall := ThreeSumSharpTail.full_d_call_total (n : ℝ) (D n : ℝ) (g n : ℝ) s C C'
    (Td n (D n) (queryCap n (D n))) (queryCap n (D n) : ℝ) hD1r hn1 hs0 hsHalf
    hgLo hgHi hfit hC hC' (Nat.cast_nonneg _) (Nat.floor_le (by positivity))
    (hlop n (D n) (queryCap n (D n)) hD1 hDle)
  have hcall' :
      4 * (n : ℝ) * g n * (Td n (D n) (queryCap n (D n)) + C' * ((n : ℝ) ^ 2 / Real.sqrt (D n)))
        ≤ (256 * C + 32 * C') * X := by
    calc
      _ = 4 * (n : ℝ) * g n * (Td n (D n) (queryCap n (D n)) + C' * (n : ℝ) ^ 2 / Real.sqrt (D n)) := by ring
      _ ≤ (64 * C + 8 * C') * (S * (Real.log (D n) + 1) ^ 2) := hcall
      _ ≤ (64 * C + 8 * C') * (S * (4 * Real.log n ^ 2)) := by gcongr
      _ = (256 * C + 32 * C') * (S * Real.log n ^ 2) := by ring
      _ ≤ (256 * C + 32 * C') * X := by gcongr
  have hextra : C' * (termScans n (g n) κ + termPrime strassen n (D n) + termBuild n (D n) (g n)) ≤ 4 * C' * X :=
    ThreeSumSharpTail.full_d_extra_total n (D n) (g n) a s κ C' hn3 hD1 hDle hs0 hsHalf
      hgLo hgHi hbuild hprime hκ hC'
  have htotal : T n u ≤ (256 * C + 36 * C') * X := by
    have ht := h17 n κ u hD16 hDn hg1 hgsqrt hκ hu
    linarith
  have hsave : (D n : ℝ) ^ (-s / 2) ≤ 2 * (n : ℝ) ^ (-(a * s / 2)) := by
    have hroot0 : 0 < (n : ℝ) ^ a := Real.rpow_pos_of_pos hn0 _
    have hlow : (n : ℝ) ^ a / 2 ≤ D n := by linarith
    calc
      (D n : ℝ) ^ (-s / 2) ≤ ((n : ℝ) ^ a / 2) ^ (-s / 2) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hlow (by linarith)
      _ = ((n : ℝ) ^ a) ^ (-s / 2) / (2 : ℝ) ^ (-s / 2) := Real.div_rpow hroot0.le (by norm_num) _
      _ = (2 : ℝ) ^ (s / 2) * (n : ℝ) ^ (-(a * s / 2)) := by
        rw [← Real.rpow_mul hn0.le, show -s / 2 = -(s / 2) by ring,
          Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul, mul_comm]
        congr 1
        ring
      _ ≤ (2 : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-(a * s / 2)) :=
        mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)) (by positivity)
      _ = 2 * (n : ℝ) ^ (-(a * s / 2)) := by rw [Real.rpow_one]
  have hcube : (n : ℝ) ^ 3 * (n : ℝ) ^ (-(a * s / 2)) = (n : ℝ) ^ (3 - a * s / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hn0]
    congr 1 <;> push_cast <;> ring
  calc
    T n u ≤ (256 * C + 36 * C') * X := htotal
    _ ≤ (256 * C + 36 * C') * (κ * ((n : ℝ) ^ 3 * (2 * (n : ℝ) ^ (-(a * s / 2))) * Real.log n ^ 2)) := by
      rw [hX, hS]
      gcongr
    _ = 2 * (256 * C + 36 * C') * (κ * ((n : ℝ) ^ (3 - a * s / 2) * Real.log n ^ 2)) := by
      rw [← hcube]
      ring

#print axioms solution
