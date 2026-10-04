-- Prove2me | solution 1 for PolygonalArcEndpointDiskCappedTaperModel
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T05:00:16.857991+00:00
-- url     : https://prove2.me/submissions/8466d3a6-df0c-4458-94ee-4f8673e88bc0

import Mathlib

set_option autoImplicit false

lemma cb37_sq_convex (x0 x1 y0 y1 u v A : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u + v = 1)
    (hx : x0 ^ 2 + x1 ^ 2 < A ^ 2) (hy : y0 ^ 2 + y1 ^ 2 < A ^ 2) :
    (u * x0 + v * y0) ^ 2 + (u * x1 + v * y1) ^ 2 < A ^ 2 := by
  have hv' : v = 1 - u := by linarith
  subst hv'
  have h1 : (u * x0 + (1 - u) * y0) ^ 2 + (u * x1 + (1 - u) * y1) ^ 2
      = u * (x0 ^ 2 + x1 ^ 2) + (1 - u) * (y0 ^ 2 + y1 ^ 2)
        - u * (1 - u) * ((x0 - y0) ^ 2 + (x1 - y1) ^ 2) := by ring
  rw [h1]
  have h2 : 0 ≤ u * (1 - u) * ((x0 - y0) ^ 2 + (x1 - y1) ^ 2) := by positivity
  rcases eq_or_lt_of_le hu with h | h
  · subst h; nlinarith
  · nlinarith

lemma cb37_lin (p q p' q' u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u + v = 1)
    (h : p < q) (h' : p' < q') : u * p + v * p' < u * q + v * q' := by
  rcases eq_or_lt_of_le hu with h0 | h0
  · subst h0
    have : v = 1 := by linarith
    subst this; linarith
  · nlinarith [mul_le_mul_of_nonneg_left h'.le hv]

open Set in
theorem solution (a K : ℝ) (ha : 0 < a) (hK : 0 < K) :
    let C : Set (EuclideanSpace ℝ (Fin 2)) :=
      {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < a ^ 2 ∧ -K * z 0 < z 1 ∧ z 1 < K * z 0}
    let L : Set (EuclideanSpace ℝ (Fin 2)) :=
      {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < a ^ 2 ∧ 0 < z 1 ∧ z 1 < K * z 0}
    let R : Set (EuclideanSpace ℝ (Fin 2)) :=
      {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < a ^ 2 ∧ -K * z 0 < z 1 ∧ z 1 < 0}
    let G : Set (EuclideanSpace ℝ (Fin 2)) :=
      {z | 0 < z 0 ∧ z 0 < a ∧ z 1 = 0}
    IsOpen C ∧ IsOpen L ∧ IsOpen R ∧
      IsConnected L ∧ IsConnected R ∧
      Disjoint L R ∧ (0 : EuclideanSpace ℝ (Fin 2)) ∉ C ∧
      G ⊆ C ∧ C \ G = L ∪ R := by
  intro C L R G
  have c0 : Continuous fun z : EuclideanSpace ℝ (Fin 2) => z 0 := by fun_prop
  have c1 : Continuous fun z : EuclideanSpace ℝ (Fin 2) => z 1 := by fun_prop
  set t : ℝ := a / (2 * (1 + K)) with ht
  have htpos : 0 < t := by positivity
  have hta : t * (2 * (1 + K)) = a := by
    rw [ht]; field_simp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact IsOpen.and (isOpen_lt (by fun_prop) (by fun_prop)) (IsOpen.and (isOpen_lt (by fun_prop) (by fun_prop))
      (IsOpen.and (isOpen_lt (by fun_prop) (by fun_prop)) (isOpen_lt (by fun_prop) (by fun_prop))))
  · exact IsOpen.and (isOpen_lt (by fun_prop) (by fun_prop)) (IsOpen.and (isOpen_lt (by fun_prop) (by fun_prop))
      (IsOpen.and (isOpen_lt (by fun_prop) (by fun_prop)) (isOpen_lt (by fun_prop) (by fun_prop))))
  · exact IsOpen.and (isOpen_lt (by fun_prop) (by fun_prop)) (IsOpen.and (isOpen_lt (by fun_prop) (by fun_prop))
      (IsOpen.and (isOpen_lt (by fun_prop) (by fun_prop)) (isOpen_lt (by fun_prop) (by fun_prop))))
  · refine Convex.isConnected ?_ ?_
    swap
    · refine ⟨!₂[t, K * t / 2], ?_⟩
      simp only [L, mem_setOf_eq]
      have hq : t ^ 2 + (K * t / 2) ^ 2 < a ^ 2 := by
        rw [← hta]; nlinarith [mul_pos htpos htpos, mul_pos (mul_pos hK htpos) htpos, sq_nonneg (K * t)]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> (try simp) <;> nlinarith [mul_pos hK htpos]
    · intro x hx y hy u v hu hv huv
      obtain ⟨hx1, hx2, hx3, hx4⟩ := hx
      obtain ⟨hy1, hy2, hy3, hy4⟩ := hy
      simp only [L, mem_setOf_eq, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      refine ⟨?_, cb37_sq_convex _ _ _ _ u v a hu hv huv hx2 hy2, ?_, ?_⟩
      · rcases eq_or_lt_of_le hu with h | h
        · subst h; simp at huv; subst huv; simpa using hy1
        · nlinarith [mul_nonneg hv hy1.le]
      · rcases eq_or_lt_of_le hu with h | h
        · subst h; simp at huv; subst huv; simpa using hy3
        · nlinarith [mul_nonneg hv hy3.le]
      · have := cb37_lin _ _ _ _ u v hu hv huv hx4 hy4
        linarith
  · refine Convex.isConnected ?_ ?_
    swap
    · refine ⟨!₂[t, -(K * t / 2)], ?_⟩
      simp only [R, mem_setOf_eq]
      have hq : t ^ 2 + (-(K * t / 2)) ^ 2 < a ^ 2 := by
        rw [← hta]; nlinarith [mul_pos htpos htpos, mul_pos (mul_pos hK htpos) htpos, sq_nonneg (K * t)]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> (try simp) <;> nlinarith [mul_pos hK htpos]
    · intro x hx y hy u v hu hv huv
      obtain ⟨hx1, hx2, hx3, hx4⟩ := hx
      obtain ⟨hy1, hy2, hy3, hy4⟩ := hy
      simp only [R, mem_setOf_eq, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      refine ⟨?_, cb37_sq_convex _ _ _ _ u v a hu hv huv hx2 hy2, ?_, ?_⟩
      · rcases eq_or_lt_of_le hu with h | h
        · subst h; simp at huv; subst huv; simpa using hy1
        · nlinarith [mul_nonneg hv hy1.le]
      · have := cb37_lin _ _ _ _ u v hu hv huv hx3 hy3
        linarith
      · rcases eq_or_lt_of_le hu with h | h
        · subst h; simp at huv; subst huv; simpa using hy4
        · nlinarith [mul_nonneg hv (neg_nonneg.mpr hy4.le)]
  · rw [Set.disjoint_left]
    rintro z ⟨-, -, h1, -⟩ ⟨-, -, -, h2⟩
    linarith
  · rintro ⟨h, -⟩
    simp at h
  · rintro z ⟨h1, h2, h3⟩
    refine ⟨h1, ?_, ?_, ?_⟩
    · rw [h3]; nlinarith
    · rw [h3]; nlinarith
    · rw [h3]; nlinarith
  · ext z
    simp only [C, G, L, R, mem_sdiff, mem_union, mem_setOf_eq]
    constructor
    · rintro ⟨⟨h1, h2, h3, h4⟩, hG⟩
      have hza : z 0 < a := by nlinarith [sq_nonneg (z 1)]
      have hz1 : z 1 ≠ 0 := fun h => hG ⟨h1, hza, h⟩
      rcases lt_or_gt_of_ne hz1 with h | h
      · right; exact ⟨h1, h2, h3, h⟩
      · left; exact ⟨h1, h2, h, h4⟩
    · rintro (⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩)
      · refine ⟨⟨h1, h2, by nlinarith, h4⟩, fun h => ?_⟩
        linarith [h.2.2]
      · refine ⟨⟨h1, h2, h3, by nlinarith⟩, fun h => ?_⟩
        linarith [h.2.2]
