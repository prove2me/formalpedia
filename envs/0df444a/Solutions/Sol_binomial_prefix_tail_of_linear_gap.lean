-- Prove2me | solution 1 for binomial_prefix_tail_of_linear_gap
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-09T05:46:46.836648+00:00
-- url     : https://prove2.me/submissions/e425e51d-835e-4034-a100-795c68b96adb

import Mathlib

set_option autoImplicit false

open Real
open scoped BigOperators

noncomputable section

private lemma binomial_tail_rate_pos_lt_one_local {c : ℝ} (hc : 0 < c) :
    0 < ((2 + c) / (2 * (1 + c))) * Real.rpow (1 + c) (1 / (2 + c)) ∧
      ((2 + c) / (2 * (1 + c))) * Real.rpow (1 + c) (1 / (2 + c)) < 1 := by
  let A : ℝ := (2 + c) / (2 * (1 + c))
  let B : ℝ := 1 + c
  let q : ℝ := 2 + c
  have hq : 0 < q := by dsimp [q]; linarith
  have hB : 0 < B := by dsimp [B]; linarith
  have hA : 0 < A := by
    dsimp [A]
    positivity
  have hpowpos : 0 < Real.rpow B q⁻¹ := Real.rpow_pos_of_pos hB _
  have hpos : 0 < A * Real.rpow B q⁻¹ := mul_pos hA hpowpos
  have hs : -1 ≤ c / q := by
    have hq' : 0 < q := hq
    dsimp [q]
    have : 0 ≤ c / (2 + c) := by positivity
    linarith
  have hs' : c / q ≠ 0 := by
    dsimp [q]
    positivity
  have hbern : 1 + q * (c / q) < (1 + c / q) ^ q :=
    one_add_mul_self_lt_rpow_one_add hs hs' (by dsimp [q]; linarith)
  have hbern' : B < (A⁻¹) ^ q := by
    have hleft : 1 + q * (c / q) = B := by
      dsimp [B, q]
      field_simp [hq.ne']
    have hright : 1 + c / q = A⁻¹ := by
      dsimp [A, q]
      field_simp [hA.ne', hq.ne']
      ring
    rw [hleft, hright] at hbern
    exact hbern
  have hpow : Real.rpow B q⁻¹ < A⁻¹ := by
    apply (Real.rpow_lt_rpow_iff (Real.rpow_nonneg hB.le _) (by positivity) hq).mp
    rw [← Real.rpow_mul (by positivity : 0 ≤ B)]
    rw [inv_mul_cancel₀ hq.ne', Real.rpow_one]
    exact hbern'
  constructor
  · simpa [A, B, q, one_div] using hpos
  · have hpow' : Real.rpow B q⁻¹ < 1 / A := by simpa [one_div] using hpow
    have hmul : Real.rpow B q⁻¹ * A < 1 := (lt_div_iff₀ hA).mp hpow'
    simpa [A, B, q, one_div, mul_comm] using hmul

private lemma binomial_prefix_geometric_bound_local
    (q t : ℕ) (hq : 0 < q) (htq : t ≤ q) (z : ℝ)
    (hz : 0 < z) (hz1 : z ≤ 1) :
    z ^ t * (∑ k : Fin t, (Nat.choose (q - 1) k : ℝ))
      ≤ (1 + z) ^ (q - 1) := by
  have hsum :
      (∑ k : Fin t, (Nat.choose (q - 1) k : ℝ)) =
        ∑ k ∈ Finset.range t, (Nat.choose (q - 1) k : ℝ) := by
    simpa only using
      (Fin.sum_univ_eq_sum_range (fun k : ℕ => (Nat.choose (q - 1) k : ℝ)) t)
  rw [hsum]
  have hterm : ∀ k ∈ Finset.range t,
      z ^ t * (Nat.choose (q - 1) k : ℝ) ≤
        (Nat.choose (q - 1) k : ℝ) * z ^ k := by
    intro k hk
    have hkt : k < t := Finset.mem_range.mp hk
    have hpow : z ^ t ≤ z ^ k :=
      pow_le_pow_of_le_one (le_of_lt hz) hz1 (Nat.le_of_lt hkt)
    simpa [mul_comm] using
      (mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg (Nat.choose (q - 1) k)))
  have hprefix :
      z ^ t * (∑ k ∈ Finset.range t, (Nat.choose (q - 1) k : ℝ)) ≤
        ∑ k ∈ Finset.range t, (Nat.choose (q - 1) k : ℝ) * z ^ k := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hterm
  have hfull :
      (∑ k ∈ Finset.range t, (Nat.choose (q - 1) k : ℝ) * z ^ k) ≤
        ∑ k ∈ Finset.range q, (Nat.choose (q - 1) k : ℝ) * z ^ k := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.range_subset_range.2 htq
    · intro k hk hkt
      positivity
  have hbinom :
      (∑ k ∈ Finset.range q, (Nat.choose (q - 1) k : ℝ) * z ^ k) =
        (1 + z) ^ (q - 1) := by
    have hpow := add_pow z 1 (q - 1)
    rw [Nat.sub_add_cancel hq] at hpow
    calc
      (∑ k ∈ Finset.range q, (Nat.choose (q - 1) k : ℝ) * z ^ k) =
          ∑ k ∈ Finset.range q,
            z ^ k * 1 ^ (q - 1 - k) * (Nat.choose (q - 1) k : ℝ) := by
        apply Finset.sum_congr rfl
        intro k hk
        simp [mul_comm]
      _ = (z + 1) ^ (q - 1) := hpow.symm
      _ = (1 + z) ^ (q - 1) := by rw [add_comm]
  exact hprefix.trans (hfull.trans_eq hbinom)

private lemma binomial_prefix_normalized_bound_local
    (q t : ℕ) (hq : 0 < q) (htq : t ≤ q) (z : ℝ)
    (hz : 0 < z) (hz1 : z ≤ 1) :
    (∑ k : Fin t, (Nat.choose (q - 1) k : ℝ)) / (2 : ℝ) ^ q ≤
      (1 + z) ^ (q - 1) / ((2 : ℝ) ^ q * z ^ t) := by
  have hbound := binomial_prefix_geometric_bound_local q t hq htq z hz hz1
  have hzpow : 0 < z ^ t := pow_pos hz _
  have htwo : 0 < (2 : ℝ) ^ q := pow_pos (by norm_num) _
  apply (le_div_iff₀ (mul_pos htwo hzpow)).2
  calc
    (∑ k : Fin t, (Nat.choose (q - 1) k : ℝ)) / (2 : ℝ) ^ q *
        ((2 : ℝ) ^ q * z ^ t) =
      z ^ t * (∑ k : Fin t, (Nat.choose (q - 1) k : ℝ)) := by
        field_simp [ne_of_gt htwo]
    _ ≤ (1 + z) ^ (q - 1) := hbound

theorem solution
    (c : ℝ) (hc : 0 < c) (q t : ℕ) (hq : 0 < q)
    (hqt : (2 + c) * (t : ℝ) ≤ (q : ℝ)) :
    0 < ((2 + c) / (2 * (1 + c))) * Real.rpow (1 + c) (1 / (2 + c)) ∧
      ((2 + c) / (2 * (1 + c))) * Real.rpow (1 + c) (1 / (2 + c)) < 1 ∧
      (∑ k : Fin t, (Nat.choose (q - 1) k : ℝ)) / (2 : ℝ) ^ q ≤
        (((2 + c) / (2 * (1 + c))) * Real.rpow (1 + c) (1 / (2 + c))) ^ q := by
  have h1c : 0 < 1 + c := by linarith
  have h2c : 0 < 2 + c := by linarith
  have htqR : (t : ℝ) ≤ (q : ℝ) := by
    have hct : 0 ≤ c * (t : ℝ) := mul_nonneg hc.le (Nat.cast_nonneg _)
    nlinarith
  have htq : t ≤ q := by exact_mod_cast htqR
  let z : ℝ := 1 / (1 + c)
  have hz : 0 < z := by
    dsimp [z]
    exact one_div_pos.mpr h1c
  have hz1 : z ≤ 1 := by
    dsimp [z]
    exact (div_le_iff₀ h1c).2 (by linarith)
  have hnorm := binomial_prefix_normalized_bound_local q t hq htq z hz hz1
  have htExp : (t : ℝ) ≤ (q : ℝ) / (2 + c) := by
    apply (le_div_iff₀ h2c).2
    nlinarith [hqt]
  have hpowt :
      (1 + c) ^ t ≤ Real.rpow (1 + c) ((q : ℝ) / (2 + c)) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) htExp
  have hmain :
      (1 + z) ^ (q - 1) / ((2 : ℝ) ^ q * z ^ t) ≤
        ((1 + z) / 2) ^ q * Real.rpow (1 + c) ((q : ℝ) / (2 + c)) := by
    have hbase : 1 ≤ 1 + z := by linarith
    have hqpow : (1 + z) ^ (q - 1) ≤ (1 + z) ^ q := by
      exact pow_le_pow_right₀ hbase (Nat.sub_le _ _)
    have hzpow : 0 < z ^ t := pow_pos hz _
    have htwo : 0 < (2 : ℝ) ^ q := pow_pos (by norm_num) _
    calc
      (1 + z) ^ (q - 1) / ((2 : ℝ) ^ q * z ^ t) ≤
          (1 + z) ^ q / ((2 : ℝ) ^ q * z ^ t) := by
        exact div_le_div_of_nonneg_right hqpow (le_of_lt (mul_pos htwo hzpow))
      _ = ((1 + z) / 2) ^ q * (1 + c) ^ t := by
        dsimp [z]
        have hrecip : (1 / (1 + c) : ℝ) ^ t = ((1 + c) ^ t)⁻¹ := by
          rw [div_pow]
          simp
        rw [hrecip]
        field_simp [h1c.ne', htwo.ne']
        have hfactor :
            (1 + c + 1) / (1 + c) =
              2 * ((1 + c + 1) / ((1 + c) * 2)) := by
          field_simp [h1c.ne']
        rw [hfactor, mul_pow]
      _ ≤ ((1 + z) / 2) ^ q * Real.rpow (1 + c) ((q : ℝ) / (2 + c)) := by
        exact mul_le_mul_of_nonneg_left hpowt (pow_nonneg (by linarith) _)
  have hratepow :
      Real.rpow (1 + c) ((q : ℝ) / (2 + c)) =
        (Real.rpow (1 + c) (1 / (2 + c))) ^ q := by
    rw [show (q : ℝ) / (2 + c) = (1 / (2 + c)) * (q : ℝ) by
      field_simp [h2c.ne']]
    simpa using
      (Real.rpow_mul_natCast (by linarith : 0 ≤ 1 + c) (1 / (2 + c)) q)
  have hratebase :
      ((1 + z) / 2) * Real.rpow (1 + c) (1 / (2 + c)) =
        ((2 + c) / (2 * (1 + c))) * Real.rpow (1 + c) (1 / (2 + c)) := by
    dsimp [z]
    congr 1
    field_simp [h1c.ne']
    ring
  have htail :
      (∑ k : Fin t, (Nat.choose (q - 1) k : ℝ)) / (2 : ℝ) ^ q ≤
        (((2 + c) / (2 * (1 + c))) * Real.rpow (1 + c) (1 / (2 + c))) ^ q := by
    calc
      (∑ k : Fin t, (Nat.choose (q - 1) k : ℝ)) / (2 : ℝ) ^ q ≤
          (1 + z) ^ (q - 1) / ((2 : ℝ) ^ q * z ^ t) := hnorm
      _ ≤ ((1 + z) / 2) ^ q * Real.rpow (1 + c) ((q : ℝ) / (2 + c)) := hmain
      _ = (((2 + c) / (2 * (1 + c))) *
          Real.rpow (1 + c) (1 / (2 + c))) ^ q := by
        rw [hratepow, ← mul_pow, hratebase]
  obtain ⟨hrate_pos, hrate_lt_one⟩ := binomial_tail_rate_pos_lt_one_local hc
  exact ⟨hrate_pos, hrate_lt_one, htail⟩

#print axioms solution
