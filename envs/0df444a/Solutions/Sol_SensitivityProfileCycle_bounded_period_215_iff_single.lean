-- Prove2me | solution 1 for SensitivityProfileCycle.bounded_period_215_iff_single
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-24T13:43:48.576559+00:00
-- url     : https://prove2.me/submissions/33bda400-2055-4819-a0d5-0963351d0410

import Theorems.Thm_SensitivityProfileCycle_scaled_radius_lower
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/- Uses the regular-tournament count and the uniform degree estimate from the
   accepted fixed-vertex proof, submission 3105c597-c367-4dd0-8f18-88fe5aec5f1f. -/
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

private theorem power_doubling (y : ℕ) (hy : 0 < y) :
    2*y^y ≤ (y+1)^y := by
  have grow (k : ℕ) : y^k*(y+k) ≤ y*(y+1)^k := by
    induction k with
    | zero => simp
    | succ k ih =>
      calc
        _ = y^k*(y*(y+k+1)) := by rw [pow_succ]; ring
        _ ≤ y^k*((y+k)*(y+1)) := Nat.mul_le_mul_left _ (by nlinarith)
        _ = (y^k*(y+k))*(y+1) := by ring
        _ ≤ (y*(y+1)^k)*(y+1) := Nat.mul_le_mul_right _ ih
        _ = _ := by rw [pow_succ,Nat.mul_assoc]
  apply Nat.le_of_mul_le_mul_left _ hy
  calc
    y*(2*y^y) = y^y*(y+y) := by ring
    _ ≤ y*(y+1)^y := grow y

private theorem integer_gap (x y R m u : ℕ) (hy : 0 < y)
    (h : x^m ≤ R*y^m) (hu : u*y ≤ m) (hR : R < 2^u) : x ≤ y := by
  by_contra! H
  have unit : 2*y^y ≤ x^y := (power_doubling y hy).trans (Nat.pow_le_pow_left H _)
  have block : 2^u*y^(u*y) ≤ x^(u*y) := by
    rw [Nat.mul_comm u y]
    simpa only [mul_pow, ← pow_mul] using Nat.pow_le_pow_left unit u
  obtain ⟨j,hj⟩ := Nat.exists_eq_add_of_le hu
  have reaches : 2^u*y^m ≤ x^m := by
    rw [hj,pow_add,pow_add,← Nat.mul_assoc]
    exact Nat.mul_le_mul block (Nat.pow_le_pow_left (Nat.le_of_lt H) _)
  have bound := Nat.le_of_mul_le_mul_right (reaches.trans h) (Nat.pow_pos hy)
  omega

private theorem single_precision (C : Certificate) (k u : ℕ)
    (hc : qualifies C k)
    (hu : u * (C.vertices^C.period)^20 ≤ k+1) (hr : C.radius < 2^u) :
    C.radius^43 ≤ (C.vertices^C.period)^20 := by
  let G := C.vertices^C.period
  apply integer_gap _ (G^20) C.radius (k+1) u
    (Nat.pow_pos (Nat.pow_pos (by have := C.vertices_gt_one; omega))) _ hu hr
  calc
    (C.radius^43)^(k+1) = C.radius^(43*(k+1)) := (pow_mul ..).symm
    _ = C.radius^(43*k+42+1) := by rw [show 43*(k+1) = 43*k+42+1 by omega]
    _ = C.radius * C.radius^(43*k+42) := by rw [pow_succ,Nat.mul_comm]
    _ ≤ C.radius * G^(20*(k+1)) := Nat.mul_le_mul_left _ hc.2
    _ = C.radius * (G^20)^(k+1) := by rw [pow_mul]

theorem solution :
    (∀ (C : SensitivityProfileCycle.Certificate) (k u : ℕ), 1 < C.radius →
      C.radius^(43*k+42) ≤ (C.vertices^C.period)^(20*(k+1)) →
      u*(C.vertices^C.period)^20 ≤ k+1 → C.radius < 2^u →
      C.radius^43 ≤ (C.vertices^C.period)^20) ∧
    ((∃ L : ℕ, ∀ k : ℕ, ∃ C : SensitivityProfileCycle.Certificate,
        C.period ≤ L ∧ 1 < C.radius ∧
        C.radius^(43*k+42) ≤ (C.vertices^C.period)^(20*(k+1))) ↔
      ∃ C : SensitivityProfileCycle.Certificate, 1 < C.radius ∧
        C.radius^43 ≤ (C.vertices^C.period)^20) := by
  refine ⟨fun C k u h₁ h₂ => single_precision C k u ⟨h₁,h₂⟩, ?_⟩
  constructor
  · rintro ⟨L, all⟩
    let k := max 2 (9*L*131072^(20*L))
    obtain ⟨C,hL,hR,hk⟩ := all k
    have hc : qualifies C k := ⟨hR,hk⟩
    have hd := tail_approx C (Nat.le_max_left _ _) hc
    have hV : C.vertices < 131072 := by rw [vertex_count C]; omega
    have hvp : C.vertices^C.period < 131072^L := by
      exact (Nat.pow_lt_pow_left hV (Nat.ne_of_gt C.period_pos)).trans_le
        (Nat.pow_le_pow_right (by decide) hL)
    have small : C.radius^2 ≤ C.vertices^C.period := by
      have at0 := (earlier (Nat.zero_le k) hc).2
      apply (Nat.pow_le_pow_iff_left (by decide : 20 ≠ 0)).mp
      rw [← pow_mul]
      exact (Nat.pow_le_pow_right (by omega) (by decide : 2*20 ≤ 42)).trans (by simpa using at0)
    have bound : C.radius < 2^(9*L) := by
      apply (Nat.pow_lt_pow_iff_left (by decide : 2 ≠ 0)).mp
      calc
        C.radius^2 < 131072^L := small.trans_lt hvp
        _ ≤ ((2:ℕ)^18)^L := Nat.pow_le_pow_left (by decide) _
        _ = (2^(9*L))^2 := by rw [← pow_mul, ← pow_mul, show 18*L = 9*L*2 by omega]
    refine ⟨C,hR,single_precision C k (9*L) hc ?_ bound⟩
    calc
      9*L*(C.vertices^C.period)^20 ≤ 9*L*(131072^L)^20 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hvp.le _)
      _ = 9*L*131072^(20*L) := by rw [← pow_mul, Nat.mul_comm L 20]
      _ ≤ k+1 := (Nat.le_max_right _ _).trans (Nat.le_succ _)
  · rintro ⟨C,hR,hc⟩
    refine ⟨C.period, fun k => ⟨C,le_rfl,hR,?_⟩⟩
    calc
      C.radius^(43*k+42) ≤ C.radius^(43*(k+1)) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      _ = (C.radius^43)^(k+1) := pow_mul .. 
      _ ≤ ((C.vertices^C.period)^20)^(k+1) := Nat.pow_le_pow_left hc _
      _ = (C.vertices^C.period)^(20*(k+1)) := (pow_mul ..).symm
