-- Prove2me | solution 1 for SensitivityProfileCycle.crossing_215_vertex_window
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-24T09:11:24.201927+00:00
-- url     : https://prove2.me/submissions/5ae7d703-9a4f-4ad4-8ae2-589d6e7721e4

import Theorems.Thm_SensitivityProfileCycle_scaled_radius_lower
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

open SensitivityProfileCycle
open scoped BigOperators Classical

set_option autoImplicit false

private theorem vertex_count (C : Certificate) : C.vertices = 2*C.degree+1 := by
  classical
  let e (i j : Fin C.vertices) : ℕ := if C.adj i j then 1 else 0
  have row (i : Fin C.vertices) : ∑ j, e i j = C.degree :=
    (Finset.card_filter (C.adj i) Finset.univ).symm.trans (C.outdegree i)
  have pair (i j : Fin C.vertices) : e i j+e j i = if i ≠ j then 1 else 0 := by
    by_cases h : i=j
    · subst j
      simp [e, C.loopless i]
    · by_cases a : C.adj i j
      · simp [e,h,a,(C.complement h).mp a]
      · have b : C.adj j i := (C.complement (Ne.symm h)).mpr a
        simp [e,h,a,b]
  have pairs (i : Fin C.vertices) : ∑ j, (e i j+e j i) = C.vertices-1 := by
    simp_rw [pair]
    rw [← Finset.card_filter]
    have hf : Finset.univ.filter (fun j : Fin C.vertices => i ≠ j) = Finset.univ.erase i := by
      ext j
      simp [ne_comm]
    rw [hf, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  have both : ∑ i, ∑ j, (e i j+e j i) = C.vertices*C.degree+C.vertices*C.degree := by
    simp_rw [Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun i j => e j i)]
    simp [row]
  have vpos : 0 < C.vertices := by have := C.vertices_gt_one; omega
  have fact : C.vertices*(C.vertices-1) = C.vertices*(C.degree+C.degree) := by
    simpa [pairs, Nat.mul_add] using both
  have := Nat.eq_of_mul_eq_mul_left vpos fact
  omega

private def B (s d : ℕ) : ℕ :=
  min (s*(2*d+1)) (min (2*s*(d+1)) (s*(d+2)+Nat.sqrt (8*d*s^2)))

private theorem necessary (C : Certificate) (hc : C.radius^43 ≤ (C.vertices^C.period)^20) (s : ℕ) :
    B s C.degree ^43 ≤ s^43*(2*C.degree+1)^40 := by
  have hs := SensitivityProfileCycle.scaled_radius_lower C s
  rw [vertex_count C] at hc hs
  change B s C.degree ^ C.period ≤ _ at hs
  apply (Nat.pow_le_pow_iff_left (Nat.ne_of_gt C.period_pos)).mp
  calc
    (B s C.degree^43)^C.period = (B s C.degree^C.period)^43 := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm 43]
    _ ≤ (s^C.period*C.radius^2)^43 := Nat.pow_le_pow_left hs _
    _ = (s^43)^C.period*(C.radius^43)^2 := by
      rw [mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul, Nat.mul_comm C.period 43, Nat.mul_comm 2 43]
    _ ≤ (s^43)^C.period*(((2*C.degree+1)^C.period)^20)^2 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hc 2)
    _ = (s^43*(2*C.degree+1)^40)^C.period := by
      rw [mul_pow]
      apply congrArg (fun x => (s^43)^C.period*x)
      rw [← pow_mul, ← pow_mul, ← pow_mul]
      apply congrArg (fun n : ℕ => (2*C.degree+1)^n)
      omega

private theorem B_monotone (s : ℕ) : Monotone (B s) := by
  intro x y h
  unfold B
  apply min_le_min (Nat.mul_le_mul_left _ (by omega))
  apply min_le_min (Nat.mul_le_mul_left _ (by omega))
  apply Nat.add_le_add (Nat.mul_le_mul_left _ (by omega))
  apply Nat.sqrt_le_sqrt
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h)

-- Consecutive intervals are closed. Each interval uses only its two endpoints.
private def intervalsPass (s lo : ℕ) : List ℕ → Bool
  | [] => true
  | hi :: rest => decide (s^43*(2*hi+1)^40 < B s lo^43) && intervalsPass s (hi+1) rest

private def stop (lo : ℕ) : List ℕ → ℕ
  | [] => lo
  | hi :: rest => stop (hi+1) rest

private theorem interval_exclusion (s d lo : ℕ) (ends : List ℕ)
    (hpass : intervalsPass s lo ends = true) (hlo : lo ≤ d) (hstop : d < stop lo ends) :
    s^43*(2*d+1)^40 < B s d^43 := by
  induction ends generalizing lo with
  | nil => simp [stop] at hstop; omega
  | cons hi rest ih =>
    simp only [intervalsPass, Bool.and_eq_true, decide_eq_true_eq] at hpass
    by_cases h : d ≤ hi
    · exact lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega : 2*d+1 ≤ 2*hi+1) 40))
        (lt_of_lt_of_le hpass.1 (Nat.pow_le_pow_left (B_monotone _ hlo) _))
    · exact ih (hi+1) hpass.2 (by omega) hstop

private theorem tail (d : ℕ) (h : 65536 ≤ d) : (2*d+1)^40 < B 1 d^43 := by
  have hd : 0 < d := by omega
  have hb : d ≤ B 1 d := by unfold B; simp only [le_min_iff]; omega
  have scalar : 9^40 < 4^40 * d^3 := lt_of_lt_of_le (by decide : (9:ℕ)^40 < 4^40*65536^3)
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h _))
  have hh : 4^40*(2*d+1)^40 < 4^40*d^43 := calc
    _ = (4*(2*d+1))^40 := (mul_pow ..).symm
    _ ≤ (9*d)^40 := Nat.pow_le_pow_left (by omega) _
    _ = 9^40*d^40 := mul_pow ..
    _ < (4^40*d^3)*d^40 := (Nat.mul_lt_mul_right (Nat.pow_pos hd)).mpr scalar
    _ = _ := by rw [Nat.mul_assoc, ← pow_add]
  exact lt_of_lt_of_le (Nat.lt_of_mul_lt_mul_left hh) (Nat.pow_le_pow_left hb _)

private def smallChecks : List ℕ :=
  [1, 2, 3, 4, 6, 8, 11, 14, 17, 20, 23, 25,
   27, 29, 31, 33, 34, 35, 36, 37, 38, 39, 40, 41]

private def largeChecks : List ℕ :=
  [6204, 6205, 6206, 6207, 6208, 6209, 6210, 6211, 6212, 6213, 6214, 6215,
   6216, 6217, 6218, 6219, 6220, 6221, 6223, 6225, 6227, 6229, 6231, 6233,
   6235, 6237, 6239, 6242, 6245, 6248, 6251, 6254, 6257, 6261, 6265, 6269,
   6273, 6277, 6282, 6287, 6292, 6298, 6304, 6310, 6317, 6324, 6331, 6339,
   6347, 6356, 6365, 6375, 6385, 6396, 6408, 6420, 6433, 6447, 6462, 6477,
   6493, 6510, 6528, 6547, 6567, 6589, 6612, 6636, 6662, 6689, 6718, 6749,
   6782, 6817, 6854, 6893, 6935, 6979, 7026, 7076, 7130, 7187, 7248, 7313,
   7382, 7456, 7535, 7620, 7710, 7807, 7911, 8022, 8142, 8270, 8408, 8557,
   8717, 8890, 9077, 9279, 9498, 9736, 9995, 10277, 10584, 10920, 11288, 11692,
   12136, 12626, 13168, 13769, 14437, 15182, 16016, 16953, 18009, 19205, 20565, 22118,
   23901, 25958, 28345, 31131, 34404, 38275, 42888, 48427, 55134, 63329, 65535]

set_option maxRecDepth 4096 in
private theorem small_pass : intervalsPass 100000 1 smallChecks = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem large_pass : intervalsPass 100000 6204 largeChecks = true := by decide +kernel

theorem solution (C : SensitivityProfileCycle.Certificate)
    (hc : C.radius^43 ≤ (C.vertices^C.period)^20) :
    85 ≤ C.vertices ∧ C.vertices ≤ 12407 := by
  have hv := vertex_count C
  have hpos := C.vertices_gt_one
  have hn := necessary C hc 100000
  have hlarge : C.degree < 65536 := by
    by_contra! h
    have h1 := necessary C hc 1
    simp only [one_pow, one_mul] at h1
    exact (Nat.not_lt_of_le h1) (tail _ h)
  constructor
  · by_contra! h
    have hlo : 1 ≤ C.degree := by omega
    have hstop : C.degree < stop 1 smallChecks := by
      change C.degree < 42
      omega
    exact (Nat.not_lt_of_le hn) (interval_exclusion _ _ _ _ small_pass hlo hstop)
  · by_contra! h
    have hlo : 6204 ≤ C.degree := by omega
    have hstop : C.degree < stop 6204 largeChecks := hlarge
    exact (Nat.not_lt_of_le hn) (interval_exclusion _ _ _ _ large_pass hlo hstop)
