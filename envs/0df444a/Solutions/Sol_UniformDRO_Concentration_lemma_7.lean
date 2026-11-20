-- Prove2me | solution 1 for UniformDRO.Concentration.lemma_7
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-19T15:38:04.607371+00:00
-- url     : https://prove2.me/submissions/a6e0919e-55a3-4a03-a7bc-b1f29ab93edf

import Mathlib
import Definitions.Def_UniformDRO_Concentration_RobustRisk

open Finset

/-- superadditivity of `x ^ q`, `q ≥ 1`, on nonnegative reals -/
lemma sum_rpow_le_rpow_sum' {d : ℕ} (a : Fin d → ℝ) (ha : ∀ i, 0 ≤ a i) {q : ℝ} (hq : 1 ≤ q) :
    ∑ i, a i ^ q ≤ (∑ i, a i) ^ q := by
  set S := ∑ i, a i with hS
  have hS0 : 0 ≤ S := sum_nonneg (fun i _ => ha i)
  have hle : ∀ i, a i ≤ S := fun i => single_le_sum (fun j _ => ha j) (mem_univ i)
  calc ∑ i, a i ^ q = ∑ i, a i * a i ^ (q - 1) := by
        refine sum_congr rfl (fun i _ => ?_)
        rcases (ha i).eq_or_lt with h | h
        · rw [← h, Real.zero_rpow (by linarith), zero_mul]
        · rw [← Real.rpow_one_add' h.le (by linarith)]; congr 1; ring
    _ ≤ ∑ i, a i * S ^ (q - 1) := by
        refine sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left ?_ (ha i))
        exact Real.rpow_le_rpow (ha i) (hle i) (by linarith)
    _ = S ^ q := by
        rw [← sum_mul, ← hS]
        rcases hS0.eq_or_lt with h | h
        · rw [← h, zero_mul, Real.zero_rpow (by linarith)]
        · rw [← Real.rpow_one_add' h.le (by linarith)]; congr 1; ring

/-- Jensen / power mean: `(∑ b) ^ s ≤ d ^ (s - 1) ∑ b ^ s` for `s ≥ 1` -/
lemma jensen' {d : ℕ} (b : Fin d → ℝ) (hb : ∀ i, 0 ≤ b i) {s : ℝ} (hs : 1 ≤ s) :
    (∑ i, b i) ^ s ≤ (d : ℝ) ^ (s - 1) * ∑ i, b i ^ s := by
  have := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg (s := (univ : Finset (Fin d))) hs
    (fun i _ => hb i)
  simpa using this


open UniformDRO.Concentration

/-- the unnormalised ℓ_q norm -/
noncomputable def Nq {n : ℕ} (q : ℝ) (y : Fin n → ℝ) : ℝ := (∑ i, |y i| ^ q) ^ (1 / q)

lemma Nq_nonneg {n : ℕ} (q : ℝ) (y : Fin n → ℝ) : 0 ≤ Nq q y :=
  Real.rpow_nonneg (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (abs_nonneg _) _)) _

lemma Nq_lip {n : ℕ} (q : ℝ) (hq : 1 ≤ q) (y y' : Fin n → ℝ) : |Nq q y - Nq q y'| ≤ Nq q (fun i => y i - y' i) := by
  have h1 := Real.Lp_add_le (s := Finset.univ) (f := fun i => y i - y' i) (g := y') hq
  have h2 := Real.Lp_add_le (s := Finset.univ) (f := fun i => y' i - y i) (g := y) hq
  simp only [sub_add_cancel] at h1 h2
  have hsym : Nq q (fun i => y' i - y i) = Nq q (fun i => y i - y' i) := by
    unfold Nq; congr 1; refine Finset.sum_congr rfl (fun i _ => ?_); rw [abs_sub_comm]
  rw [abs_le]; unfold Nq at *
  constructor
  · have := hsym; unfold Nq at this; linarith
  · linarith

/-- comparison of `N_q` with the Euclidean norm -/
lemma Nq_le_l2 {n : ℕ} (hn : 0 < n) (q : ℝ) (hq : 1 < q) (d : Fin n → ℝ) :
    (n : ℝ) ^ (-(1 / q)) * Nq q d ≤ (n : ℝ) ^ (-(1 / max 2 q)) * Real.sqrt (∑ i, d i ^ 2) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hS0 : 0 ≤ ∑ i, d i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hsq : Real.sqrt (∑ i, d i ^ 2) = (∑ i, d i ^ 2) ^ (1 / (2 : ℝ)) := Real.sqrt_eq_rpow _
  have hb0 : ∀ i, 0 ≤ |d i| ^ q := fun i => Real.rpow_nonneg (abs_nonneg _) _
  have hq0 : 0 < q := by linarith
  rcases le_total 2 q with h2q | hq2
  · -- q ≥ 2: ℓ_q ≤ ℓ_2
    rw [max_eq_right h2q]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hs : 1 ≤ q / 2 := by rw [le_div_iff₀ (by norm_num)]; linarith
    have hsup := sum_rpow_le_rpow_sum' (fun i => d i ^ 2) (fun i => sq_nonneg _) hs
    have e : ∀ i, (d i ^ 2) ^ (q / 2) = |d i| ^ q := by
      intro i
      rw [← sq_abs, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]; congr 1; push_cast; ring
    simp only [e] at hsup
    unfold Nq
    rw [hsq]
    calc (∑ i, |d i| ^ q) ^ (1 / q) ≤ ((∑ i, d i ^ 2) ^ (q / 2)) ^ (1 / q) :=
          Real.rpow_le_rpow (Finset.sum_nonneg (fun i _ => hb0 i)) hsup (by positivity)
      _ = (∑ i, d i ^ 2) ^ (1 / 2 : ℝ) := by
          rw [← Real.rpow_mul hS0]; congr 1; field_simp
  · -- q ≤ 2: power mean
    rw [max_eq_left hq2]
    have hs : 1 ≤ 2 / q := by rw [le_div_iff₀ hq0]; linarith
    have hJ := jensen' (fun i => |d i| ^ q) hb0 hs
    have e : ∀ i, (|d i| ^ q) ^ (2 / q) = d i ^ 2 := by
      intro i
      rw [← Real.rpow_mul (abs_nonneg _), mul_div_cancel₀ _ hq0.ne', ← sq_abs]; norm_cast
    simp only [e] at hJ
    -- (Σ b)^(2/q) ≤ n^(2/q - 1) Σ d²; take square roots
    have hN : Nq q d ≤ (n : ℝ) ^ (1 / q - 1 / 2) * (∑ i, d i ^ 2) ^ (1 / 2 : ℝ) := by
      unfold Nq
      have hB0 : 0 ≤ ∑ i, |d i| ^ q := Finset.sum_nonneg (fun i _ => hb0 i)
      have h1 := Real.rpow_le_rpow (Real.rpow_nonneg hB0 _) hJ (by norm_num : (0 : ℝ) ≤ 1 / 2)
      rw [← Real.rpow_mul hB0, Real.mul_rpow (by positivity) hS0, ← Real.rpow_mul hn0.le] at h1
      convert h1 using 2
      · field_simp
      · congr 1; field_simp
    calc (n : ℝ) ^ (-(1 / q)) * Nq q d
        ≤ (n : ℝ) ^ (-(1 / q)) * ((n : ℝ) ^ (1 / q - 1 / 2) * (∑ i, d i ^ 2) ^ (1 / 2 : ℝ)) := by gcongr
      _ = (n : ℝ) ^ (-(1 / 2 : ℝ)) * Real.sqrt (∑ i, d i ^ 2) := by
          rw [hsq, ← mul_assoc, ← Real.rpow_add hn0]; congr 2; ring

theorem solution (k : ℝ) (hk : 1 < k) (n : ℕ) (hn : 0 < n) (y y' : Fin n → ℝ) :
    |((1 / n : ℝ) * ∑ i, |y i| ^ kstar k) ^ (1 / kstar k) -
        ((1 / n : ℝ) * ∑ i, |y' i| ^ kstar k) ^ (1 / kstar k)| ≤
      (n : ℝ) ^ (-(1 / max 2 (kstar k))) * Real.sqrt (∑ i, (y i - y' i) ^ 2) := by
  set q := kstar k with hq
  have hq1 : 1 < q := by
    rw [hq]; unfold kstar; rw [lt_div_iff₀ (by linarith)]; linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hscale : ∀ z : Fin n → ℝ, ((1 / n : ℝ) * ∑ i, |z i| ^ q) ^ (1 / q) = (n : ℝ) ^ (-(1 / q)) * Nq q z := by
    intro z
    unfold Nq
    rw [Real.mul_rpow (by positivity) (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (abs_nonneg _) _)),
      one_div (n : ℝ), Real.inv_rpow hn0.le, Real.rpow_neg hn0.le]
  rw [hscale, hscale, ← mul_sub, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hn0 _)]
  calc (n : ℝ) ^ (-(1 / q)) * |Nq q y - Nq q y'|
      ≤ (n : ℝ) ^ (-(1 / q)) * Nq q (fun i => y i - y' i) := by
        gcongr; exact Nq_lip q hq1.le y y'
    _ ≤ _ := Nq_le_l2 hn q hq1 _
