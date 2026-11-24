-- Prove2me | solution 1 for SensitivityProfileCycle.cofinal_215_iff_fixed_vertices
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-24T09:20:46.709282+00:00
-- url     : https://prove2.me/submissions/3105c597-c367-4dd0-8f18-88fe5aec5f1f

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

private def qualifies (C : Certificate) (k : ℕ) : Prop :=
  1 < C.radius ∧ C.radius^(43*k+42) ≤ (C.vertices^C.period)^(20*(k+1))

private theorem earlier {C : Certificate} {k j : ℕ} (hkj : k ≤ j)
    (hj : qualifies C j) : qualifies C k := by
  refine ⟨hj.1, ?_⟩
  let G := C.vertices^C.period
  apply (Nat.pow_le_pow_iff_left (Nat.succ_ne_zero j)).mp
  calc
    (C.radius^(43*k+42))^(j+1) = C.radius^((43*k+42)*(j+1)) := (pow_mul ..).symm
    _ ≤ C.radius^((43*j+42)*(k+1)) := Nat.pow_le_pow_right (by have := hj.1; omega) (by nlinarith)
    _ = (C.radius^(43*j+42))^(k+1) := pow_mul ..
    _ ≤ (G^(20*(j+1)))^(k+1) := Nat.pow_le_pow_left hj.2 _
    _ = (G^(20*(k+1)))^(j+1) := by
      rw [← pow_mul G (20*(j+1)) (k+1), ← pow_mul G (20*(k+1)) (j+1)]
      apply congrArg (fun n : ℕ => G^n)
      ring

private theorem scaled_test (C : Certificate) (p q : ℕ)
    (hc : C.radius^p ≤ (C.vertices^C.period)^q) (s : ℕ) :
    B s C.degree ^p ≤ s^p*(2*C.degree+1)^(q*2) := by
  have hs := SensitivityProfileCycle.scaled_radius_lower C s
  rw [vertex_count C] at hc hs
  change B s C.degree ^ C.period ≤ _ at hs
  apply (Nat.pow_le_pow_iff_left (Nat.ne_of_gt C.period_pos)).mp
  calc
    (B s C.degree^p)^C.period = (B s C.degree^C.period)^p := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm p]
    _ ≤ (s^C.period*C.radius^2)^p := Nat.pow_le_pow_left hs _
    _ = (s^p)^C.period*(C.radius^p)^2 := by
      rw [mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul, Nat.mul_comm C.period p, Nat.mul_comm 2 p]
    _ ≤ (s^p)^C.period*(((2*C.degree+1)^C.period)^q)^2 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hc 2)
    _ = (s^p*(2*C.degree+1)^(q*2))^C.period := by
      rw [mul_pow]
      apply congrArg (fun x => (s^p)^C.period*x)
      rw [← pow_mul, ← pow_mul, ← pow_mul]
      apply congrArg (fun n : ℕ => (2*C.degree+1)^n)
      ring

private theorem tail_approx (C : Certificate) {k : ℕ} (hk : 2 ≤ k)
    (hc : qualifies C k) : C.degree < 65536 := by
  have h2 := earlier hk hc
  have hj := scaled_test C 128 60 h2.2 1
  simp only [one_pow, one_mul] at hj
  by_contra! h
  let d := C.degree
  have hd : 65536 ≤ d := h
  have hpos : 0 < d := by omega
  have hb : d ≤ B 1 d := by unfold B; simp only [le_min_iff]; omega
  have strong : d^32 ≤ (2*d+1)^30 := by
    apply (Nat.pow_le_pow_iff_left (by decide : 4 ≠ 0)).mp
    rw [← pow_mul, ← pow_mul]
    exact (Nat.pow_le_pow_left hb 128).trans hj
  have scalar : 33^30 < 16^30 * d^2 := lt_of_lt_of_le (by decide : (33:ℕ)^30 < 16^30*65536^2)
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hd _))
  have hh : 16^30*(2*d+1)^30 < 16^30*d^32 := calc
    _ = (16*(2*d+1))^30 := (mul_pow ..).symm
    _ ≤ (33*d)^30 := Nat.pow_le_pow_left (by omega) _
    _ = 33^30*d^30 := mul_pow ..
    _ < (16^30*d^2)*d^30 := (Nat.mul_lt_mul_right (Nat.pow_pos hpos)).mpr scalar
    _ = _ := by rw [Nat.mul_assoc, ← pow_add]
  exact (Nat.not_lt_of_le strong) (Nat.lt_of_mul_lt_mul_left hh)

private theorem constant_degree (H : ∀ k, ∃ C, qualifies C k) :
    ∃ d : Fin 65536, ∀ k, ∃ C, C.degree = d.val ∧ qualifies C k := by
  classical
  by_contra! fail
  choose test htest using fail
  let j := max 2 (Finset.univ.sup test)
  obtain ⟨C,hC⟩ := H j
  let d : Fin 65536 := ⟨C.degree,tail_approx C (Nat.le_max_left _ _) hC⟩
  have hj : test d ≤ j :=
    (Finset.le_sup (f := test) (Finset.mem_univ d)).trans (Nat.le_max_right _ _)
  exact htest d C rfl (earlier hj hC)

private theorem power_comparison (x y a : ℕ) (hy : 0 < y) (h : ∀ k, x^k ≤ y^k*a) : x ≤ y := by
  by_contra! bad
  have gain (k : ℕ) : y^k*(y+k) ≤ y*(y+1)^k := by
    induction k with
    | zero => simp
    | succ k ih =>
      calc
        _ = y^k*(y*(y+k+1)) := by rw [pow_succ]; ring
        _ ≤ y^k*((y+k)*(y+1)) := Nat.mul_le_mul_left _ (by nlinarith)
        _ = (y^k*(y+k))*(y+1) := by ring
        _ ≤ (y*(y+1)^k)*(y+1) := Nat.mul_le_mul_right _ ih
        _ = _ := by rw [pow_succ, Nat.mul_assoc]
  let k := y*a+1
  have big : y^k*(y+k) ≤ y^k*(y*a) := calc
    _ ≤ y*(y+1)^k := gain k
    _ ≤ y*x^k := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left bad _)
    _ ≤ y*(y^k*a) := Nat.mul_le_mul_left _ (h k)
    _ = _ := by ring
  have hc := Nat.le_of_mul_le_mul_left big (Nat.pow_pos hy)
  dsimp [k] at hc
  omega

private theorem limit_at_degree (d s : ℕ) (hs : 0 < s) (hd : 0 < d)
    (H : ∀ k, ∃ C, C.degree=d ∧ qualifies C k) :
    B s d ^43 ≤ s^43*(2*d+1)^40 := by
  let v := 2*d+1
  have hv : 0 < v := by dsimp [v]; omega
  have hb : 0 < B s d := by
    unfold B
    simp only [lt_min_iff]
    exact ⟨Nat.mul_pos hs hv,Nat.mul_pos (Nat.mul_pos (by decide) hs) (by omega),
      by have := Nat.mul_pos hs (show 0<d+2 by omega); omega⟩
  apply power_comparison _ _ (s^42*v^40) (Nat.mul_pos (Nat.pow_pos hs) (Nat.pow_pos hv))
  intro k
  obtain ⟨C,hC,hk⟩ := H k
  have h := scaled_test C _ _ hk.2 s
  rw [hC] at h
  calc
    (B s d^43)^k ≤ (B s d^43)^k*B s d^42 := Nat.le_mul_of_pos_right _ (Nat.pow_pos hb)
    _ = B s d^(43*k+42) := by rw [pow_add, pow_mul]
    _ ≤ s^(43*k+42)*v^((20*(k+1))*2) := h
    _ = (s^43*v^40)^k*(s^42*v^40) := by
      rw [show 20*(k+1)*2=40*k+40 by omega, pow_add, pow_add, pow_mul, pow_mul, mul_pow]
      ring

theorem solution :
    (∀ k : ℕ, ∃ C : SensitivityProfileCycle.Certificate,
      1 < C.radius ∧ C.radius^(43*k+42) ≤ (C.vertices^C.period)^(20*(k+1))) ↔
    ∃ K : ℕ, 85 ≤ K ∧ K ≤ 12407 ∧ ∀ k : ℕ, ∃ C : SensitivityProfileCycle.Certificate,
      C.vertices = K ∧ 1 < C.radius ∧ C.radius^(43*k+42) ≤ (C.vertices^C.period)^(20*(k+1)) := by
  constructor
  · intro H
    obtain ⟨d,hd⟩ := constant_degree H
    obtain ⟨C,hC,_⟩ := hd 0
    have hpos := C.vertices_gt_one
    rw [vertex_count C,hC] at hpos
    have htest := limit_at_degree d.val 100000 (by decide) (by omega) hd
    have small : 42 ≤ d.val := by
      by_contra! h
      exact (Nat.not_lt_of_le htest) (interval_exclusion _ _ _ _ small_pass (by omega)
        (show d.val < 42 by omega))
    have large : d.val ≤ 6203 := by
      by_contra! h
      exact (Nat.not_lt_of_le htest) (interval_exclusion _ _ _ _ large_pass h d.isLt)
    refine ⟨2*d.val+1,by omega,by omega,?_⟩
    intro k
    obtain ⟨F,hF,hk⟩ := hd k
    exact ⟨F,by rw [vertex_count F,hF],hk⟩
  · rintro ⟨_,_,_,h⟩ k
    obtain ⟨C,_,hk⟩ := h k
    exact ⟨C,hk⟩
