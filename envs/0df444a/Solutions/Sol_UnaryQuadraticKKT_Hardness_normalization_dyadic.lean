-- Prove2me | solution 1 for UnaryQuadraticKKT.Hardness.normalization_dyadic
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T17:38:37.456745+00:00
-- url     : https://prove2.me/submissions/cbfcc85b-a36c-4b79-8b0a-f3714198154b

import Mathlib
import Definitions.Def_UnaryQuadraticKKT_Hardness_Normalization

set_option autoImplicit false

namespace UQKKTNormalizationAux
open Finset UnaryQuadraticKKT.Hardness NetworkEquilibriumCLS.LinearNash

theorem foldl_lcm_dvd_init (l : List ℕ) (a : ℕ) : a ∣ l.foldl Nat.lcm a := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih => exact (Nat.dvd_lcm_left a b).trans (ih (Nat.lcm a b))

theorem dvd_foldl_lcm (l : List ℕ) (a x : ℕ) (hx : x ∈ l) : x ∣ l.foldl Nat.lcm a := by
  induction l generalizing a with
  | nil => simp at hx
  | cons b l ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.1 hx with rfl | hx
    · exact (Nat.dvd_lcm_right a x).trans (foldl_lcm_dvd_init l _)
    · exact ih _ hx

theorem foldl_lcm_pos (l : List ℕ) (a : ℕ) (ha : 0 < a) (hl : ∀ x ∈ l, 0 < x) :
    0 < l.foldl Nat.lcm a := by
  induction l generalizing a with
  | nil => simpa using ha
  | cons b l ih =>
    simp only [List.foldl_cons]
    exact ih _ (Nat.lcm_pos ha (hl b (by simp))) (fun x hx => hl x (by simp [hx]))

theorem le_foldl_max_init (l : List ℕ) (a : ℕ) : a ≤ l.foldl max a := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih => exact (le_max_left a b).trans (ih (max a b))

theorem le_foldl_max (l : List ℕ) (a x : ℕ) (hx : x ∈ l) : x ≤ l.foldl max a := by
  induction l generalizing a with
  | nil => simp at hx
  | cons b l ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.1 hx with rfl | hx
    · exact (le_max_right a x).trans (le_foldl_max_init l _)
    · exact ih _ hx

/-- Binary expansion of a natural number below `2 ^ L` through its `testBit`s. -/
theorem nat_eq_sum_bits (L : ℕ) : ∀ a : ℕ, a < 2 ^ L →
    (a : ℝ) = ∑ i ∈ range L, (if a.testBit i then (1 : ℝ) else 0) * 2 ^ i := by
  induction L with
  | zero =>
    intro a ha
    have : a = 0 := by simpa using ha
    subst this; simp
  | succ L ih =>
    intro a ha
    rw [Finset.sum_range_succ']
    have h2 : a / 2 < 2 ^ L := by rw [pow_succ] at ha; omega
    have hih := ih (a / 2) h2
    have hsum : ∑ i ∈ range L, (if a.testBit (i + 1) then (1 : ℝ) else 0) * 2 ^ (i + 1)
        = 2 * ((a / 2 : ℕ) : ℝ) := by
      rw [hih, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← Nat.testBit_div_two, pow_succ]; ring
    rw [hsum]
    have key : (a : ℝ) = 2 * ((a / 2 : ℕ) : ℝ) + ((a % 2 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.div_add_mod a 2).symm
    rcases Nat.mod_two_eq_zero_or_one a with h | h
    · rw [h] at key; simp [h]; push_cast at key; linarith
    · rw [h] at key; simp [h]; push_cast at key; linarith

theorem denominatorLCM_pos {n : ℕ} (p : Quadratic n) : 0 < denominatorLCM p := by
  unfold denominatorLCM
  refine foldl_lcm_pos _ _ one_pos ?_
  intro x hx
  obtain ⟨t, -, rfl⟩ := List.mem_map.1 hx
  exact Rat.den_pos _

theorem den_dvd_denominatorLCM {n : ℕ} (p : Quadratic n) (t : Monomial n) (ht : t ∈ slots n) :
    (coefficient p t).den ∣ denominatorLCM p := by
  unfold denominatorLCM
  exact dvd_foldl_lcm _ _ _ (List.mem_map.2 ⟨t, ht, rfl⟩)

theorem lcm_mul_coefficient {n : ℕ} (p : Quadratic n) (t : Monomial n) (ht : t ∈ slots n) :
    (denominatorLCM p : ℚ) * coefficient p t = (clearedCoefficient p t : ℚ) := by
  obtain ⟨k, hk⟩ := den_dvd_denominatorLCM p t ht
  have e : (denominatorLCM p : ℚ) * coefficient p t = ((k * (coefficient p t).num : ℤ) : ℚ) := by
    rw [hk]; push_cast
    rw [← Rat.mul_den_eq_num (coefficient p t)]; ring
  unfold clearedCoefficient
  rw [e, Rat.num_intCast]

theorem natAbs_cleared_lt {n : ℕ} (p : Quadratic n) (t : Monomial n) (ht : t ∈ slots n) :
    (clearedCoefficient p t).natAbs < 2 ^ normalizationLength p := by
  have h1 : (clearedCoefficient p t).natAbs ≤ maximumMagnitude p := by
    unfold maximumMagnitude
    exact le_foldl_max _ _ _ (List.mem_map.2 ⟨t, ht, rfl⟩)
  have h2 := Nat.lt_size_self (maximumMagnitude p)
  unfold normalizationLength
  rw [Nat.size_eq_bits_len]
  omega

theorem coefficient_normalized {n : ℕ} (p : Quadratic n) (t : Monomial n) :
    coefficient (normalized p) t = normalizationScale p * coefficient p t := by
  cases t with
  | linear i => simp [coefficient, normalized]
  | quadratic i j =>
    by_cases h : i = j
    · subst h; simp [coefficient, normalized]; ring
    · simp [coefficient, normalized, h]

theorem sourceGradient_normalized {n : ℕ} (p : Quadratic n) (x : Fin n → ℝ) (i : Fin n) :
    sourceGradient (normalized p) x i = (normalizationScale p : ℝ) * sourceGradient p x i := by
  simp only [sourceGradient, normalized, Rat.cast_mul, mul_add, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

theorem normalizationScale_pos {n : ℕ} (p : Quadratic n) : (0 : ℝ) < normalizationScale p := by
  have h := denominatorLCM_pos p
  unfold normalizationScale
  push_cast
  positivity

end UQKKTNormalizationAux

open Finset NetworkEquilibriumCLS.LinearNash UnaryQuadraticKKT.Hardness UQKKTNormalizationAux

theorem solution {n : ℕ} (hn : 0 < n) (p : Quadratic n) :
    (∀ x : Fin n → ℝ, QuadraticKKT p x ↔ QuadraticKKT (normalized p) x) ∧
    (∀ t ∈ slots n,
      (coefficientSign p t = -1 ∨ coefficientSign p t = 1) ∧
      (coefficient (normalized p) t : ℝ) = (coefficientSign p t : ℝ) *
        ∑ j : Fin (normalizationLength p),
          (if coefficientBit p t j then (1 : ℝ) else 0) *
            (2 : ℝ) ^ (-((j.val + 1 : ℕ) : ℤ))) := by
  have hs := normalizationScale_pos p
  refine ⟨fun x => ?_, fun t ht => ?_⟩
  · unfold QuadraticKKT BoxSigns
    simp only [sourceGradient_normalized]
    refine and_congr Iff.rfl (forall_congr' fun i => ?_)
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have := h1 h; nlinarith
      · have := h2 h; nlinarith
    · rintro ⟨h1, h2⟩
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have := h1 h
        by_contra hc
        have hc' : 0 < sourceGradient p x i := lt_of_not_ge hc
        have : 0 < (normalizationScale p : ℝ) * sourceGradient p x i := mul_pos hs hc'
        linarith
      · have := h2 h
        by_contra hc
        have hc' : sourceGradient p x i < 0 := by
          have := lt_of_not_ge hc; linarith
        have : (normalizationScale p : ℝ) * sourceGradient p x i < 0 :=
          mul_neg_of_pos_of_neg hs hc'
        linarith
  · refine ⟨by unfold coefficientSign; split_ifs <;> simp, ?_⟩
    set L := normalizationLength p with hL
    set z := clearedCoefficient p t with hz
    have hlt : z.natAbs < 2 ^ L := natAbs_cleared_lt p t ht
    -- the normalized coefficient is z / 2^L
    have hcoef : (coefficient (normalized p) t : ℝ) = (z : ℝ) / 2 ^ L := by
      have hq : coefficient (normalized p) t = (z : ℚ) / 2 ^ L := by
        rw [coefficient_normalized, normalizationScale, ← lcm_mul_coefficient p t ht]
        ring
      rw [hq]; push_cast; ring
    -- the signed magnitude
    have hsign : (z : ℝ) = (coefficientSign p t : ℝ) * (z.natAbs : ℝ) := by
      have habs : ((z.natAbs : ℕ) : ℝ) = |(z : ℝ)| := by
        rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
      rw [habs]
      unfold coefficientSign
      rw [← hz]
      split_ifs with h
      · have : (z : ℝ) < 0 := by exact_mod_cast h
        rw [abs_of_neg this]; push_cast; ring
      · have : (0 : ℝ) ≤ z := by exact_mod_cast (not_lt.1 h)
        rw [abs_of_nonneg this]; push_cast; ring
    -- the digit sum
    have hsum : ∑ j : Fin L, (if coefficientBit p t j then (1 : ℝ) else 0) *
        (2 : ℝ) ^ (-((j.val + 1 : ℕ) : ℤ)) = (z.natAbs : ℝ) / 2 ^ L := by
      have e1 : ∑ j : Fin L, (if coefficientBit p t j then (1 : ℝ) else 0) *
          (2 : ℝ) ^ (-((j.val + 1 : ℕ) : ℤ))
          = ∑ j ∈ range L, (if z.natAbs.testBit (L - (j + 1)) then (1 : ℝ) else 0) *
            (2 : ℝ) ^ (-((j + 1 : ℕ) : ℤ)) :=
        (Finset.sum_range (fun j => (if z.natAbs.testBit (L - (j + 1)) then (1 : ℝ) else 0) *
            (2 : ℝ) ^ (-((j + 1 : ℕ) : ℤ)))).symm
      set f : ℕ → ℝ := fun i => (if z.natAbs.testBit i then (1 : ℝ) else 0) * 2 ^ i / 2 ^ L
        with hf
      have e2 : ∑ j ∈ range L, (if z.natAbs.testBit (L - (j + 1)) then (1 : ℝ) else 0) *
            (2 : ℝ) ^ (-((j + 1 : ℕ) : ℤ)) = ∑ j ∈ range L, f (L - 1 - j) := by
        refine Finset.sum_congr rfl (fun j hj => ?_)
        have hj' : j < L := Finset.mem_range.1 hj
        have hidx : L - (j + 1) = L - 1 - j := by omega
        rw [hf]
        simp only
        rw [hidx, mul_div_assoc]
        congr 1
        rw [zpow_neg, zpow_natCast]
        have h2 : (2 : ℝ) ^ L = 2 ^ (L - 1 - j) * 2 ^ (j + 1) := by
          rw [← pow_add]; congr 1; omega
        rw [h2]
        field_simp
      rw [e1, e2, Finset.sum_range_reflect f L, hf]
      simp only
      rw [← Finset.sum_div, ← nat_eq_sum_bits L _ hlt]
    rw [hsum, hcoef, hsign]
    ring
