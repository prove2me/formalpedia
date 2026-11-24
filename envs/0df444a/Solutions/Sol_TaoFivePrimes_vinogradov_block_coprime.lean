-- Prove2me | solution 1 for TaoFivePrimes.vinogradov_block_coprime
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-18T10:21:04.920299+00:00
-- url     : https://prove2.me/submissions/b5097703-5d01-44b0-9f94-2f72dad18af7

import Mathlib
import Definitions.Def_TaoFivePrimes_TypeIEnvelopeInterfaces
import Theorems.Thm_TaoFivePrimes_TypeISafeOddVinogradov_safe_odd_vinogradov_short_real_interval_bound

set_option maxHeartbeats 1000000

open Finset
open TaoFivePrimes.TypeISharpVinogradov
open TaoFivePrimes.TypeISafeOddVinogradov

namespace TaoFivePrimesBlockCoprime

/-- `((z.toNat : ℕ) : ℤ) = z` for nonnegative `z`. -/
lemma toNat_cast_of_nonneg {z : ℤ} (hz : 0 ≤ z) : ((z.toNat : ℕ) : ℤ) = z :=
  Int.toNat_of_nonneg hz

/-- Real form of `toNat_cast_of_nonneg`. -/
lemma toNat_cast_of_nonneg_real {z : ℤ} (hz : 0 ≤ z) : (((z.toNat : ℕ) : ℝ)) = (z : ℝ) := by
  exact_mod_cast toNat_cast_of_nonneg hz

/-- `((z.natAbs : ℕ) : ℤ) = -z` for negative `z`. -/
lemma natAbs_cast_of_neg {z : ℤ} (hz : z < 0) : ((z.natAbs : ℕ) : ℤ) = -z := by
  have h : ((((-z).natAbs : ℕ)) : ℤ) = -z := Int.natAbs_of_nonneg (by omega)
  simpa only [Int.natAbs_neg] using h

/-- Oddness transfers between `ℕ` and `ℤ`. -/
lemma nat_odd_iff_int_odd (d : ℕ) : Odd (d : ℤ) ↔ Odd d := by
  constructor
  · rintro ⟨k, hk⟩
    have hk0 : 0 ≤ k := by
      by_contra hneg
      have hkneg : k ≤ -1 := by omega
      have : (d : ℤ) ≤ -1 := by
        rw [hk]
        omega
      omega
    lift k to ℕ using hk0
    exact ⟨k, by exact_mod_cast hk⟩
  · rintro ⟨k, hk⟩
    exact ⟨(k : ℤ), by exact_mod_cast hk⟩

/-- For odd `z`, halving is exact. -/
lemma two_mul_div_two_add_one (z : ℤ) (h : Odd z) : 2 * ((z - 1) / 2) + 1 = z := by
  obtain ⟨k, rfl⟩ := h
  omega

/-- Membership in `realOddInterval`, in terms of real bounds. -/
lemma mem_realOddInterval {x y : ℝ} {n : ℕ} (hy : 0 ≤ y) :
    n ∈ realOddInterval x y ↔ (n : ℝ) ≤ y ∧ x < (n : ℝ) ∧ Odd n := by
  unfold realOddInterval
  constructor
  · intro h
    rw [Finset.mem_filter, Finset.mem_range] at h
    obtain ⟨hr, hx, ho⟩ := h
    rw [Nat.lt_add_one_iff] at hr
    exact ⟨(Nat.le_floor_iff hy).mp hr, hx, ho⟩
  · intro h
    obtain ⟨hny, hx, ho⟩ := h
    rw [Finset.mem_filter, Finset.mem_range, Nat.lt_add_one_iff]
    exact ⟨(Nat.le_floor_iff hy).mpr hny, hx, ho⟩

/-- `safeCappedCosecant` is invariant under `(α, θ) ↦ (-α, -θ)`. -/
lemma safeCappedCosecant_neg (A B α θ : ℝ) (n : ℤ) :
    safeCappedCosecant A B (Real.pi * α * (n : ℝ) + θ)
      = safeCappedCosecant A B (Real.pi * (-α) * (n : ℝ) + (-θ)) := by
  unfold TaoFivePrimes.TypeISafeOddVinogradov.safeCappedCosecant
  have harg : Real.pi * (-α) * (n : ℝ) + (-θ)
      = -(Real.pi * α * (n : ℝ) + θ) := by ring
  rw [harg, Real.sin_neg, abs_neg]
  by_cases hs : Real.sin (Real.pi * α * (n : ℝ) + θ) = 0
  · simp [hs]
  · simp [hs]

/-- The odd naturals in `(1, 2q+1]`, reindexed as `2k+1` for `k ∈ [1,q]`. -/
lemma sum_int_odd_Icc_eq_realOddInterval (q : ℕ) (g : ℝ → ℝ) :
    (∑ k ∈ Finset.Icc (1 : ℤ) (q : ℤ), g (2 * k + 1))
      = ∑ n ∈ realOddInterval 1 (2 * (q : ℝ) + 1), g (n : ℝ) := by
  refine Finset.sum_bij (fun k _ => (2 * k + 1).toNat) ?_ ?_ ?_ ?_
  · intro k hk
    rw [Finset.mem_Icc] at hk
    have hk0 : (0 : ℤ) ≤ 2 * k + 1 := by omega
    have hcast : (((2 * k + 1).toNat : ℕ) : ℤ) = 2 * k + 1 := toNat_cast_of_nonneg hk0
    have hcastR : (((2 * k + 1).toNat : ℕ) : ℝ) = ((2 * k + 1 : ℤ) : ℝ) :=
      toNat_cast_of_nonneg_real hk0
    rw [mem_realOddInterval (by positivity)]
    refine ⟨?_, ?_, ?_⟩
    · rw [hcastR]
      have h : (2 * k + 1 : ℤ) ≤ 2 * (q : ℤ) + 1 := by omega
      exact_mod_cast h
    · rw [hcastR]
      have h : (1 : ℤ) < 2 * k + 1 := by omega
      exact_mod_cast h
    · have ho : Odd (2 * k + 1 : ℤ) := ⟨k, by ring⟩
      have ho' : Odd (((2 * k + 1).toNat : ℕ) : ℤ) := by rw [hcast]; exact ho
      exact (nat_odd_iff_int_odd _).mp ho'
  · intro k hk k' hk' heq
    rw [Finset.mem_Icc] at hk hk'
    have h1 := toNat_cast_of_nonneg (by omega : (0 : ℤ) ≤ 2 * k + 1)
    have h2 := toNat_cast_of_nonneg (by omega : (0 : ℤ) ≤ 2 * k' + 1)
    have h3 : (((2 * k + 1).toNat : ℕ) : ℤ) = (((2 * k' + 1).toNat : ℕ) : ℤ) := by rw [heq]
    rw [h1, h2] at h3
    omega
  · intro n hn
    rw [mem_realOddInterval (by positivity)] at hn
    obtain ⟨hny, hn1, hno⟩ := hn
    have hnoZ : Odd (n : ℤ) := (nat_odd_iff_int_odd n).mpr hno
    have hz : 2 * (((n : ℤ) - 1) / 2) + 1 = (n : ℤ) :=
      two_mul_div_two_add_one _ hnoZ
    refine ⟨((n : ℤ) - 1) / 2, ?_, ?_⟩
    · rw [Finset.mem_Icc]
      have hny' : (n : ℤ) ≤ 2 * (q : ℤ) + 1 := by exact_mod_cast hny
      have hn1' : (1 : ℤ) < (n : ℤ) := by exact_mod_cast hn1
      omega
    · show (2 * (((n : ℤ) - 1) / 2) + 1).toNat = n
      rw [hz, Int.toNat_natCast]
  · intro k hk
    rw [Finset.mem_Icc] at hk
    have harg : (2 : ℝ) * (k : ℝ) + 1 = ((((2 * k + 1).toNat : ℕ)) : ℝ) := by
      have h' : (2 * k + 1 : ℤ) = (((2 * k + 1).toNat : ℕ) : ℤ) :=
        (Int.toNat_of_nonneg (by omega)).symm
      exact_mod_cast h'
    rw [harg]

/-- The single-block estimate, normalized to a natural modulus `a` coprime to `q`. -/
lemma block_bound_norm
    (B : ℝ) (hB : 0 ≤ B) (q : ℕ) (hq : 2 ≤ q)
    (A' α θ : ℝ) (hA' : 0 ≤ A') (a : ℕ) (haq : Nat.Coprime a q)
    (β : ℝ) (hα : α = (a : ℝ) / q + β) (hβ : |β| ≤ 1 / (q : ℝ) ^ 2)
    (m : ℤ) :
    (∑ n ∈ Finset.Ioc m (m + (q : ℤ)),
        (if Real.sin (Real.pi * α * (n : ℝ) + θ) = 0 then A'
          else min A' (B / |Real.sin (Real.pi * α * (n : ℝ) + θ)|)))
      ≤ 2 * A' + (2 / Real.pi) * B * (q : ℝ) * Real.log (4 * q) := by
  have hcap : ∀ n : ℤ,
      (if Real.sin (Real.pi * α * (n : ℝ) + θ) = 0 then A'
        else min A' (B / |Real.sin (Real.pi * α * (n : ℝ) + θ)|))
      = safeCappedCosecant A' B (Real.pi * α * (n : ℝ) + θ) := fun n => rfl
  simp_rw [hcap]
  have hstep1 : (∑ n ∈ Finset.Ioc m (m + (q : ℤ)),
        safeCappedCosecant A' B (Real.pi * α * (n : ℝ) + θ))
      = ∑ k ∈ Finset.Icc (1 : ℤ) (q : ℤ),
        safeCappedCosecant A' B (Real.pi * α * ((m + k : ℤ) : ℝ) + θ) := by
    refine Finset.sum_bij (fun n _ => n - m) ?_ ?_ ?_ ?_
    · intro n hn
      rw [Finset.mem_Ioc] at hn
      rw [Finset.mem_Icc]
      omega
    · intro n hn n' hn' heq
      omega
    · intro k hk
      rw [Finset.mem_Icc] at hk
      refine ⟨k + m, ?_, ?_⟩
      · rw [Finset.mem_Ioc]
        omega
      · omega
    · intro n hn
      show safeCappedCosecant A' B (Real.pi * α * (n : ℝ) + θ)
          = safeCappedCosecant A' B (Real.pi * α * ((m + (n - m) : ℤ) : ℝ) + θ)
      congr 1
      push_cast
      ring
  have hstep2 : (∑ k ∈ Finset.Icc (1 : ℤ) (q : ℤ),
        safeCappedCosecant A' B (Real.pi * α * ((m + k : ℤ) : ℝ) + θ))
      = ∑ k ∈ Finset.Icc (1 : ℤ) (q : ℤ),
        safeCappedCosecant A' B (Real.pi * (α / 2) * (2 * (k : ℝ) + 1)
          + (θ + Real.pi * α * (m : ℝ) - Real.pi * (α / 2))) := by
    apply Finset.sum_congr rfl
    intro k hk
    congr 1
    push_cast
    ring
  have hstep3 : (∑ k ∈ Finset.Icc (1 : ℤ) (q : ℤ),
        safeCappedCosecant A' B (Real.pi * (α / 2) * (2 * (k : ℝ) + 1)
          + (θ + Real.pi * α * (m : ℝ) - Real.pi * (α / 2))))
      = ∑ n ∈ realOddInterval 1 (2 * (q : ℝ) + 1),
        safeCappedCosecant A' B (Real.pi * (α / 2) * (n : ℝ)
          + (θ + Real.pi * α * (m : ℝ) - Real.pi * (α / 2))) :=
    sum_int_odd_Icc_eq_realOddInterval q
      (fun z : ℝ => safeCappedCosecant A' B (Real.pi * (α / 2) * z
        + (θ + Real.pi * α * (m : ℝ) - Real.pi * (α / 2))))
  have hsafod := safe_odd_vinogradov_short_real_interval_bound a q 1 (2 * (q : ℝ) + 1)
    (by norm_num) (by linarith [show (0 : ℝ) ≤ (q : ℝ) by positivity]) (by linarith) hq haq
    (α / 2) β (θ + Real.pi * α * (m : ℝ) - Real.pi * (α / 2)) A' B
    (by rw [hα]; ring) hβ hA' hB
  rw [hstep1, hstep2, hstep3]
  exact hsafod

/-- Sign-reflected version of `block_bound_norm`. -/
lemma block_bound_flip
    (B : ℝ) (hB : 0 ≤ B) (q : ℕ) (hq : 2 ≤ q)
    (A' α θ : ℝ) (hA' : 0 ≤ A') (a : ℕ) (haq : Nat.Coprime a q)
    (β : ℝ) (hα : -α = (a : ℝ) / q + β) (hβ : |β| ≤ 1 / (q : ℝ) ^ 2)
    (m : ℤ) :
    (∑ n ∈ Finset.Ioc m (m + (q : ℤ)),
        (if Real.sin (Real.pi * α * (n : ℝ) + θ) = 0 then A'
          else min A' (B / |Real.sin (Real.pi * α * (n : ℝ) + θ)|)))
      ≤ 2 * A' + (2 / Real.pi) * B * (q : ℝ) * Real.log (4 * q) := by
  have hmain := block_bound_norm B hB q hq A' (-α) (-θ) hA' a haq β hα hβ m
  refine le_trans ?_ hmain
  apply Finset.sum_le_sum
  intro n hn
  apply le_of_eq
  change safeCappedCosecant A' B (Real.pi * α * (n : ℝ) + θ)
      = safeCappedCosecant A' B (Real.pi * (-α) * (n : ℝ) + (-θ))
  exact safeCappedCosecant_neg A' B α θ n

end TaoFivePrimesBlockCoprime

theorem solution
    (B : ℝ) (hB : 0 ≤ B) (q : ℕ) (hq : 0 < q)
    (A' alpha' beta' theta' : ℝ) (a' : ℤ) (hA' : 0 ≤ A')
    (ha'q : Nat.Coprime a'.natAbs q)
    (halpha' : alpha' = (a' : ℝ) / q + beta') (hbeta' : |beta'| ≤ 1 / (q : ℝ) ^ 2)
    (m : ℤ) :
    (∑ n ∈ Finset.Ioc m (m + (q : ℤ)),
        (if Real.sin (Real.pi * alpha' * (n : ℝ) + theta') = 0 then A'
          else min A' (B / |Real.sin (Real.pi * alpha' * (n : ℝ) + theta')|)))
      ≤ 2 * A' + (2 / Real.pi) * B * (q : ℝ) * Real.log (4 * q) := by
  rcases eq_or_lt_of_le (show 1 ≤ q by omega) with hq1 | hq2
  · subst q
    simp only [Nat.cast_one] at *
    have hsingle : Finset.Ioc m (m + (1 : ℤ)) = {m + 1} := by
      ext n
      rw [Finset.mem_Ioc, Finset.mem_singleton]
      omega
    rw [hsingle, Finset.sum_singleton]
    push_cast
    have hle : (if Real.sin (Real.pi * alpha' * ((m : ℝ) + 1) + theta') = 0 then A'
        else min A' (B / |Real.sin (Real.pi * alpha' * ((m : ℝ) + 1) + theta')|)) ≤ A' := by
      split_ifs with h
      · exact le_rfl
      · exact min_le_left _ _
    have h1 : 0 ≤ 2 / Real.pi := by positivity
    have h2 : 0 ≤ Real.log (4 * (1 : ℝ)) := (Real.log_pos (by norm_num)).le
    have h3 : 0 ≤ (2 / Real.pi) * B * 1 * Real.log (4 * 1) :=
      mul_nonneg (mul_nonneg (mul_nonneg h1 hB) (by norm_num)) h2
    linarith [hle, hA', h3]
  · by_cases ha' : 0 ≤ a'
    · set a : ℕ := a'.natAbs with ha
      have hacast : (a : ℤ) = a' := Int.natAbs_of_nonneg ha'
      have haR : (a : ℝ) = (a' : ℝ) := by exact_mod_cast hacast
      have hα : alpha' = (a : ℝ) / (q : ℝ) + beta' := by
        rw [halpha', haR]
      exact TaoFivePrimesBlockCoprime.block_bound_norm B hB q (by omega) A' alpha' theta'
        hA' a ha'q beta' hα hbeta' m
    · have ha'neg : a' < 0 := not_le.mp ha'
      set a : ℕ := a'.natAbs with ha
      have hacast : (a : ℤ) = -a' := TaoFivePrimesBlockCoprime.natAbs_cast_of_neg ha'neg
      have haR : (a : ℝ) = -(a' : ℝ) := by exact_mod_cast hacast
      have hα : -alpha' = (a : ℝ) / (q : ℝ) + (-beta') := by
        rw [halpha', haR]
        ring
      have hβ : |(-beta')| ≤ 1 / (q : ℝ) ^ 2 := by simpa using hbeta'
      exact TaoFivePrimesBlockCoprime.block_bound_flip B hB q (by omega) A' alpha' theta'
        hA' a ha'q (-beta') hα hβ m
