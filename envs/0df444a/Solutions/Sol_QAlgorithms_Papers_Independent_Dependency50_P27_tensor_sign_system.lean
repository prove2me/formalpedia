-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P27.tensor_sign_system
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T11:58:13.793391+00:00
-- url     : https://prove2.me/submissions/7b6b5af7-5446-4dfc-8424-1f7289f0185c

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P27

noncomputable section

open QAlgorithms.Papers.Independent.Dependency50.P27
open Polynomial

lemma S171T_sgr {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] (y : R) :
    sgr y = ((SignType.sign y : SignType) : ℤ) := by
  unfold sgr
  rcases lt_trichotomy y 0 with h | h | h
  · simp [h.ne, not_lt.2 h.le, sign_neg h]
  · simp [h]
  · simp [h.ne', h, sign_pos h]

def S171T_idx (v : ℤ) : Fin 3 := if v = 1 then 0 else if v = -1 then 1 else 2

lemma S171T_cases {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] (y : R) :
    sgr y = 1 ∨ sgr y = -1 ∨ sgr y = 0 := by
  unfold sgr; split_ifs <;> simp

lemma S171T_sv {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] (y : R) (i : Fin 3) :
    signValue i = sgr y ↔ i = S171T_idx (sgr y) := by
  rcases S171T_cases y with h | h | h <;> rw [h] <;> fin_cases i <;> simp [signValue, S171T_idx]

lemma S171T_ct {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] (y : R) (j : Fin 3) :
    ctmat1 (S171T_idx (sgr y)) j = ((sgr y : ℤ) : ℚ) ^ exponentValue j := by
  rcases S171T_cases y with h | h | h <;> rw [h] <;> fin_cases j <;> simp [S171T_idx, ctmat1, exponentValue]

lemma S171T_prod {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] {n : ℕ} (f : Fin n → R) :
    sgr (∏ k, f k) = ∏ k, sgr (f k) := by
  simp only [S171T_sgr]
  rw [show SignType.sign (∏ k, f k) = ∏ k, SignType.sign (f k) from map_prod signHom f Finset.univ]
  exact map_prod (SignType.castHom : SignType →*₀ ℤ) _ _

def S171T_inv : Matrix (Fin 3) (Fin 3) ℚ := !![1/2, -1/2, 0; 1/2, 1/2, -1; 0, 0, 1]

lemma S171T_mul : ctmat1 * S171T_inv = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [ctmat1, S171T_inv, Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num


theorem solution {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [PolynomialIVT R] (n : ℕ) (qs : Fin n → Polynomial R) (z : List R) :
    tvec z qs = Matrix.vecMul (cvec z qs) (tensorMatrix n) ∧
    IsUnit (tensorMatrix n) := by
  refine ⟨?_, ?_⟩
  · funext e
    induction z with
    | nil =>
      simp [tvec, cvec, taq, Matrix.vecMul, dotProduct]
    | cons x z ih =>
      have h1 : tvec (x :: z) qs e = (sgr ((∏ k, qs k ^ exponentValue (e k)).eval x) : ℚ) + tvec z qs e := by
        simp [tvec, taq]
      have h2 : ∀ s, cvec (x :: z) qs s =
          (if s = (fun k => S171T_idx (sgr ((qs k).eval x))) then 1 else 0) + cvec z qs s := by
        intro s
        simp only [cvec, List.filter_cons]
        have : (∀ k, sgr ((qs k).eval x) = signValue (s k)) ↔ s = (fun k => S171T_idx (sgr ((qs k).eval x))) := by
          rw [funext_iff]
          exact forall_congr' (fun k => by rw [eq_comm, S171T_sv])
        by_cases hs : s = (fun k => S171T_idx (sgr ((qs k).eval x)))
        · rw [if_pos (by simpa [this] using hs), if_pos hs]; simp; ring
        · rw [if_neg (by simpa [this] using hs), if_neg hs]; simp
      rw [h1, ih]
      simp only [Matrix.vecMul, dotProduct, h2, add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
      congr 1
      simp only [tensorMatrix, S171T_ct, Polynomial.eval_prod, Polynomial.eval_pow, S171T_prod]
      push_cast
      refine Finset.prod_congr rfl (fun k _ => ?_)
      rw [S171T_sgr, sign_pow, S171T_sgr]; push_cast; rfl
  · rw [Matrix.isUnit_iff_isUnit_det]
    apply Matrix.isUnit_det_of_right_inverse (B := Matrix.of fun e s => ∏ k, S171T_inv (e k) (s k))
    ext s u
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply, tensorMatrix, ← Finset.prod_mul_distrib]
    rw [← Fintype.prod_sum (fun k j => ctmat1 (s k) j * S171T_inv j (u k))]
    simp only [← Matrix.mul_apply, S171T_mul, Matrix.one_apply]
    by_cases h : s = u
    · subst h; simp
    · rw [if_neg h]
      obtain ⟨k, hk⟩ := Function.ne_iff.1 h
      exact Finset.prod_eq_zero (Finset.mem_univ k) (if_neg hk)

end
