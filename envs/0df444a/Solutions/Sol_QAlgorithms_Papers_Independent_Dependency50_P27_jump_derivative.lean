-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P27.jump_derivative
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T11:51:07.48087+00:00
-- url     : https://prove2.me/submissions/537880d7-9095-4e22-88e4-13261e5c8ee8

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P27

noncomputable section

open QAlgorithms.Papers.Independent.Dependency50.P27
open Polynomial

lemma S170bP_first (k : ℕ) : ∀ (N : ℕ) (φ : ℕ → ℤ), k < N → (∀ i < k, φ i = 0) → φ k ≠ 0 →
    firstSign ((List.range N).map φ) = φ k := by
  induction k with
  | zero =>
    intro N φ hN _ h0
    obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
    rw [List.range_succ_eq_map, List.map_cons, firstSign, if_neg h0]
  | succ k ih =>
    intro N φ hN hlt hk
    obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
    rw [List.range_succ_eq_map, List.map_cons, firstSign, if_pos (hlt 0 (by omega)), List.map_map]
    exact ih N' (φ ∘ Nat.succ) (by omega) (fun i hi => hlt (i + 1) (by omega)) hk

lemma S170bP_sgr_mul {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] {c : R} (hc : 0 < c) (y : R) :
    sgr (c * y) = sgr y := by
  unfold sgr
  rcases lt_trichotomy y 0 with h | h | h
  · have : c * y < 0 := mul_neg_of_pos_of_neg hc h
    simp [h.ne, this.ne, not_lt.2 h.le, not_lt.2 this.le]
  · simp [h]
  · have : 0 < c * y := mul_pos hc h
    simp [h.ne', this.ne', h, this]

lemma S170bP_mult {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] (x : R) (k : ℕ)
    (G : Polynomial R) (hG : G.eval x ≠ 0) :
    Polynomial.rootMultiplicity x ((Polynomial.X - Polynomial.C x) ^ k * G) = k := by
  have hG0 : G ≠ 0 := by rintro rfl; simp at hG
  rw [Polynomial.rootMultiplicity_mul (mul_ne_zero (pow_ne_zero _ (Polynomial.X_sub_C_ne_zero x)) hG0),
    Polynomial.rootMultiplicity_X_sub_C_pow, Polynomial.rootMultiplicity_eq_zero (by simpa using hG), add_zero]

lemma S170bP_right {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] (x : R) (k : ℕ)
    (G : Polynomial R) (hG : G.eval x ≠ 0) :
    rightSign ((Polynomial.X - Polynomial.C x) ^ k * G) x = sgr (G.eval x) := by
  set f := (Polynomial.X - Polynomial.C x) ^ k * G with hf
  have hG0 : G ≠ 0 := by rintro rfl; simp at hG
  have hf0 : f ≠ 0 := mul_ne_zero (pow_ne_zero _ (Polynomial.X_sub_C_ne_zero x)) hG0
  have hm : f.rootMultiplicity x = k := S170bP_mult x k G hG
  have hdiv : f /ₘ (Polynomial.X - Polynomial.C x) ^ k = G :=
    Polynomial.mul_divByMonic_cancel_left G ((Polynomial.monic_X_sub_C x).pow k)
  have hdeg : k < f.natDegree + 1 := by
    have h1 : ((Polynomial.X - Polynomial.C x) ^ k).natDegree ≤ f.natDegree :=
      Polynomial.natDegree_le_of_dvd (dvd_mul_right _ _) hf0
    rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one] at h1
    omega
  have hk : sgr ((Polynomial.derivative^[k] f).eval x) = sgr (G.eval x) := by
    have := Polynomial.eval_iterate_derivative_rootMultiplicity (p := f) (t := x)
    rw [hm, hdiv, nsmul_eq_mul] at this
    rw [this, S170bP_sgr_mul (by exact_mod_cast Nat.factorial_pos k)]
  have hlow : ∀ i < k, sgr ((Polynomial.derivative^[i] f).eval x) = 0 := by
    intro i hi
    have := Polynomial.isRoot_iterate_derivative_of_lt_rootMultiplicity (p := f) (t := x) (by rw [hm]; exact hi)
    simp [this.eq_zero, sgr]
  have hne : sgr ((Polynomial.derivative^[k] f).eval x) ≠ 0 := by
    rw [hk]; unfold sgr; split_ifs <;> simp_all
  unfold rightSign
  rw [S170bP_first k _ (fun j => sgr ((Polynomial.derivative^[j] f).eval x)) hdeg hlow hne, hk]


theorem solution {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [PolynomialIVT R] (p q : Polynomial R) (x : R)
    (hp : p ≠ 0) (hx : p.eval x = 0) :
    cauchyJump (q * p.derivative) p x = sgr (q.eval x) := by
  obtain ⟨h, hph, hndvd⟩ := p.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hp x
  have hm : 0 < p.rootMultiplicity x := (Polynomial.rootMultiplicity_pos hp).2 hx
  have hh : h.eval x ≠ 0 := fun h0 => hndvd (Polynomial.dvd_iff_isRoot.2 h0)
  set m := p.rootMultiplicity x with hmdef
  set g := Polynomial.C (m : R) * h + (Polynomial.X - Polynomial.C x) * Polynomial.derivative h with hgdef
  have e : (Polynomial.X - Polynomial.C x) ^ m = (Polynomial.X - Polynomial.C x) ^ (m - 1) * (Polynomial.X - Polynomial.C x) := by
    rw [← pow_succ, Nat.sub_add_cancel hm]
  have hder : Polynomial.derivative p = (Polynomial.X - Polynomial.C x) ^ (m - 1) * g := by
    rw [hph, Polynomial.derivative_mul, Polynomial.derivative_X_sub_C_pow, e, hgdef]; ring
  have hg0 : g.eval x ≠ 0 := by
    have hm0 : (m : R) ≠ 0 := by exact_mod_cast hm.ne'
    simp [hgdef, hm0, hh]
  have hmultd : (Polynomial.derivative p).rootMultiplicity x = m - 1 := by
    rw [hder]; exact S170bP_mult x (m - 1) g hg0
  have hd0 : Polynomial.derivative p ≠ 0 := by
    rw [hder]; exact mul_ne_zero (pow_ne_zero _ (Polynomial.X_sub_C_ne_zero x)) (by rintro h0; simp [h0] at hg0)
  unfold cauchyJump
  by_cases hq : q.eval x = 0
  · rw [if_neg]
    · simp [sgr, hq]
    · rintro ⟨hne, hodd⟩
      have hq0 : q ≠ 0 := left_ne_zero_of_mul hne
      have h1 : 0 < q.rootMultiplicity x := (Polynomial.rootMultiplicity_pos hq0).2 hq
      rw [Polynomial.rootMultiplicity_mul hne, hmultd, ← hmdef] at hodd
      have : m - (q.rootMultiplicity x + (m - 1)) = 0 := by omega
      rw [this] at hodd
      exact absurd hodd (by decide)
  · have hq0 : q ≠ 0 := by rintro rfl; simp at hq
    have hne : q * Polynomial.derivative p ≠ 0 := mul_ne_zero hq0 hd0
    have hmq : (q * Polynomial.derivative p).rootMultiplicity x = m - 1 := by
      rw [Polynomial.rootMultiplicity_mul hne, hmultd, Polynomial.rootMultiplicity_eq_zero (by simpa using hq),
        zero_add]
    have hfac : q * Polynomial.derivative p * p =
        (Polynomial.X - Polynomial.C x) ^ ((m - 1) + m) * (q * g * h) := by
      rw [hder]; conv_lhs => rw [hph]
      rw [pow_add]; ring
    have hG : (q * g * h).eval x ≠ 0 := by simp [hq, hg0, hh]
    have hrs : rightSign (q * Polynomial.derivative p * p) x = sgr (q.eval x) := by
      rw [hfac, S170bP_right x _ _ hG]
      have : (q * g * h).eval x = ((m : R) * h.eval x ^ 2) * q.eval x := by
        simp [hgdef]; ring
      rw [this, S170bP_sgr_mul]
      have hm0 : (0 : R) < m := by exact_mod_cast hm
      positivity
    rw [if_pos ⟨hne, by rw [hmq, ← hmdef]; exact ⟨0, by omega⟩⟩, hrs]
    unfold sgr
    rcases lt_or_gt_of_ne hq with h1 | h1
    · simp [h1.ne, not_lt.2 h1.le]
    · simp [h1.ne', h1, not_lt.2 h1.le]

end
