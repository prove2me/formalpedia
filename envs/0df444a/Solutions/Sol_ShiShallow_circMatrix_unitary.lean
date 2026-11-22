-- Prove2me | solution 1 for ShiShallow.circMatrix_unitary
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-13T20:53:00.934934+00:00
-- url     : https://prove2.me/submissions/1f1f6dbb-9c80-400c-9dbf-7fd9077f6c52

/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import Definitions.Def_ShiShallow_Matrix

set_option autoImplicit false

open ShiShallow

/-! ### A 2x2 unitarity criterion -/

private lemma shiUn_bool_unitary (U : Matrix Bool Bool ℂ)
    (hd : ∀ a : Bool, ∑ c : Bool, star (U c a) * U c a = 1)
    (ho : ∀ a b : Bool, a ≠ b → ∑ c : Bool, star (U c a) * U c b = 0) :
    star U * U = (1 : Matrix Bool Bool ℂ) := by
  ext a b
  rw [Matrix.mul_apply]
  first
  | (simp only [Matrix.star_apply])
  | (simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply])
  by_cases hab : a = b
  · subst hab
    rw [Matrix.one_apply_eq]
    exact hd a
  · rw [Matrix.one_apply_ne hab]
    exact ho a b hab

/-! ### The four one-qubit gates are unitary -/

private lemma shiUn_h_ff : hMat false false = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ := by
  first
  | rfl
  | (simp only [hMat, Matrix.of_apply]; done)
  | (simp [hMat]; done)

private lemma shiUn_h_ft : hMat false true = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ := by
  first
  | rfl
  | (simp only [hMat, Matrix.of_apply]; done)
  | (simp [hMat]; done)

private lemma shiUn_h_tf : hMat true false = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ := by
  first
  | rfl
  | (simp only [hMat, Matrix.of_apply]; done)
  | (simp [hMat]; done)

private lemma shiUn_h_tt : hMat true true = -(((Real.sqrt 2 : ℝ) : ℂ)⁻¹) := by
  first
  | rfl
  | (simp only [hMat, Matrix.of_apply]; done)
  | (simp [hMat]; done)

private lemma shiUn_hMat : star hMat * hMat = (1 : Matrix Bool Bool ℂ) := by
  have hR : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (2 : ℝ)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  have hinv : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = (2 : ℂ)⁻¹ := by
    rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, hR]
    first
    | (norm_num; done)
    | (push_cast; ring)
    | (simp; done)
  have hsr : star (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ := by
    rw [← Complex.ofReal_inv, ← starRingEnd_apply, Complex.conj_ofReal]
  refine shiUn_bool_unitary hMat ?_ ?_
  · intro a
    rw [Fintype.sum_bool]
    cases a
    · rw [shiUn_h_tf, shiUn_h_ff, hsr, hinv]
      norm_num
    · rw [shiUn_h_tt, shiUn_h_ft, star_neg, hsr, neg_mul_neg, hinv]
      norm_num
  · intro a b hab
    rw [Fintype.sum_bool]
    cases a <;> cases b
    · exact absurd rfl hab
    · rw [shiUn_h_tf, shiUn_h_tt, shiUn_h_ff, shiUn_h_ft, hsr]
      ring
    · rw [shiUn_h_tt, shiUn_h_tf, shiUn_h_ft, shiUn_h_ff, star_neg, hsr]
      ring
    · exact absurd rfl hab

private lemma shiUn_s_ff : sMat false false = (1 : ℂ) := by
  first
  | rfl
  | (simp only [sMat, Matrix.of_apply]; done)
  | (simp [sMat]; done)

private lemma shiUn_s_ft : sMat false true = (0 : ℂ) := by
  first
  | rfl
  | (simp only [sMat, Matrix.of_apply]; done)
  | (simp [sMat]; done)

private lemma shiUn_s_tf : sMat true false = (0 : ℂ) := by
  first
  | rfl
  | (simp only [sMat, Matrix.of_apply]; done)
  | (simp [sMat]; done)

private lemma shiUn_s_tt : sMat true true = Complex.I := by
  first
  | rfl
  | (simp only [sMat, Matrix.of_apply]; done)
  | (simp [sMat]; done)

private lemma shiUn_sMat : star sMat * sMat = (1 : Matrix Bool Bool ℂ) := by
  have hI : star Complex.I = -Complex.I := by
    rw [← starRingEnd_apply, Complex.conj_I]
  refine shiUn_bool_unitary sMat ?_ ?_
  · intro a
    rw [Fintype.sum_bool]
    cases a
    · rw [shiUn_s_tf, shiUn_s_ff, star_zero, star_one]
      ring
    · rw [shiUn_s_tt, shiUn_s_ft, hI, star_zero, neg_mul, Complex.I_mul_I]
      ring
  · intro a b hab
    rw [Fintype.sum_bool]
    cases a <;> cases b
    · exact absurd rfl hab
    · rw [shiUn_s_tf, shiUn_s_tt, shiUn_s_ff, shiUn_s_ft, star_zero, star_one]
      ring
    · rw [shiUn_s_tt, shiUn_s_tf, shiUn_s_ft, shiUn_s_ff, star_zero]
      ring
    · exact absurd rfl hab

private lemma shiUn_t_ff : tMat false false = (1 : ℂ) := by
  first
  | rfl
  | (simp only [tMat, Matrix.of_apply]; done)
  | (simp [tMat]; done)

private lemma shiUn_t_ft : tMat false true = (0 : ℂ) := by
  first
  | rfl
  | (simp only [tMat, Matrix.of_apply]; done)
  | (simp [tMat]; done)

private lemma shiUn_t_tf : tMat true false = (0 : ℂ) := by
  first
  | rfl
  | (simp only [tMat, Matrix.of_apply]; done)
  | (simp [tMat]; done)

private lemma shiUn_t_tt :
    tMat true true = Complex.exp (Complex.I * (Real.pi : ℂ) / 4) := by
  first
  | rfl
  | (simp only [tMat, Matrix.of_apply]; done)
  | (simp [tMat]; done)

private lemma shiUn_exp_unit (z : ℂ) (hz : star z = -z) :
    star (Complex.exp z) * Complex.exp z = 1 := by
  have h1 : star (Complex.exp z) = Complex.exp (star z) := by
    first
    | (rw [← starRingEnd_apply, ← Complex.exp_conj, starRingEnd_apply]; done)
    | (exact (Complex.exp_conj z).symm)
  rw [h1, hz, ← Complex.exp_add]
  first
  | (rw [neg_add_cancel, Complex.exp_zero]; done)
  | (rw [neg_add_self, Complex.exp_zero]; done)
  | (simp; done)

private lemma shiUn_tMat : star tMat * tMat = (1 : Matrix Bool Bool ℂ) := by
  have hI : star Complex.I = -Complex.I := by
    rw [← starRingEnd_apply, Complex.conj_I]
  have hpi : star ((Real.pi : ℂ) / 4) = (Real.pi : ℂ) / 4 := by
    first
    | (rw [← starRingEnd_apply, map_div₀, Complex.conj_ofReal, map_ofNat]; done)
    | (rw [← starRingEnd_apply]; simp; done)
    | (simp [← starRingEnd_apply, Complex.conj_ofReal]; done)
  have hz : star (Complex.I * (Real.pi : ℂ) / 4)
      = -(Complex.I * (Real.pi : ℂ) / 4) := by
    first
    | (rw [mul_div_assoc, star_mul, hpi, hI]; ring)
    | (rw [← starRingEnd_apply, map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal,
           map_ofNat]; ring)
  have hE := shiUn_exp_unit (Complex.I * (Real.pi : ℂ) / 4) hz
  refine shiUn_bool_unitary tMat ?_ ?_
  · intro a
    rw [Fintype.sum_bool]
    cases a
    · rw [shiUn_t_tf, shiUn_t_ff, star_zero, star_one]
      ring
    · rw [shiUn_t_tt, shiUn_t_ft, star_zero, hE]
      ring
  · intro a b hab
    rw [Fintype.sum_bool]
    cases a <;> cases b
    · exact absurd rfl hab
    · rw [shiUn_t_tf, shiUn_t_tt, shiUn_t_ff, shiUn_t_ft, star_zero, star_one]
      ring
    · rw [shiUn_t_tt, shiUn_t_tf, shiUn_t_ft, shiUn_t_ff, star_zero]
      ring
    · exact absurd rfl hab

private lemma shiUn_x_ff : xMat false false = (0 : ℂ) := by
  first
  | rfl
  | (simp only [xMat, Matrix.of_apply]; done)
  | (simp [xMat]; done)

private lemma shiUn_x_ft : xMat false true = (1 : ℂ) := by
  first
  | rfl
  | (simp only [xMat, Matrix.of_apply]; done)
  | (simp [xMat]; done)

private lemma shiUn_x_tf : xMat true false = (1 : ℂ) := by
  first
  | rfl
  | (simp only [xMat, Matrix.of_apply]; done)
  | (simp [xMat]; done)

private lemma shiUn_x_tt : xMat true true = (0 : ℂ) := by
  first
  | rfl
  | (simp only [xMat, Matrix.of_apply]; done)
  | (simp [xMat]; done)

private lemma shiUn_xMat : star xMat * xMat = (1 : Matrix Bool Bool ℂ) := by
  refine shiUn_bool_unitary xMat ?_ ?_
  · intro a
    rw [Fintype.sum_bool]
    cases a
    · rw [shiUn_x_tf, shiUn_x_ff, star_zero, star_one]
      ring
    · rw [shiUn_x_tt, shiUn_x_ft, star_zero, star_one]
      ring
  · intro a b hab
    rw [Fintype.sum_bool]
    cases a <;> cases b
    · exact absurd rfl hab
    · rw [shiUn_x_tf, shiUn_x_tt, shiUn_x_ff, shiUn_x_ft, star_zero, star_one]
      ring
    · rw [shiUn_x_tt, shiUn_x_tf, shiUn_x_ft, shiUn_x_ff, star_zero, star_one]
      ring
    · exact absurd rfl hab

/-! ### Two-point sums over basis strings -/

private lemma shiUn_two_point_sum {ι : Type} [Fintype ι] [DecidableEq ι] {A B : ι}
    (hAB : A ≠ B) (F : ι → ℂ)
    (hF : ∀ x, x ≠ A → x ≠ B → F x = 0) :
    ∑ x, F x = F A + F B := by
  have hsub : ({A, B} : Finset ι) ⊆ Finset.univ := Finset.subset_univ _
  have h1 : ∑ x ∈ ({A, B} : Finset ι), F x = ∑ x ∈ Finset.univ, F x := by
    refine Finset.sum_subset hsub ?_
    intro x _ hx
    exact hF x (fun h => hx (by simp [h])) (fun h => hx (by simp [h]))
  rw [← h1]
  exact Finset.sum_pair hAB

private lemma shiUn_update_ne {n : ℕ} (i : Fin n) (y : Bits n) :
    Function.update y i false ≠ Function.update y i true := by
  intro h
  have h1 : Function.update y i false i = Function.update y i true i := congrFun h i
  rw [Function.update_self, Function.update_self] at h1
  exact Bool.false_ne_true h1

/-! ### `apply1Matrix U i` is unitary whenever `U` is -/

private lemma shiUn_a1_entry {n : ℕ} (U : Matrix Bool Bool ℂ) (i : Fin n) (y z : Bits n) :
    apply1Matrix U i y z =
      if (∀ k, k ∉ ({i} : Finset (Fin n)) → y k = z k) then U (y i) (z i) else 0 := by
  first
  | rfl
  | (simp only [apply1Matrix, Matrix.of_apply]; done)

private lemma shiUn_row_guard {n : ℕ} (i : Fin n) (w y : Bits n)
    (h : ∀ k, k ∉ ({i} : Finset (Fin n)) → w k = y k) :
    w = Function.update y i (w i) := by
  funext k
  by_cases hk : k = i
  · rw [hk, Function.update_self]
  · rw [Function.update_of_ne hk]
    exact h k (by simpa [Finset.mem_singleton] using hk)

private lemma shiUn_a1_row_vanish {n : ℕ} (U : Matrix Bool Bool ℂ) (i : Fin n) (w y : Bits n)
    (h0 : w ≠ Function.update y i false) (h1 : w ≠ Function.update y i true) :
    apply1Matrix U i w y = 0 := by
  rw [shiUn_a1_entry]
  refine if_neg ?_
  intro hguard
  have hw : w = Function.update y i (w i) := shiUn_row_guard i w y hguard
  cases hwi : w i
  · exact h0 (by rw [hw, hwi])
  · exact h1 (by rw [hw, hwi])

private lemma shiUn_a1_row_entry {n : ℕ} (U : Matrix Bool Bool ℂ) (i : Fin n) (y z : Bits n)
    (b : Bool) (h : ∀ k, k ∉ ({i} : Finset (Fin n)) → y k = z k) :
    apply1Matrix U i (Function.update y i b) z = U b (z i) := by
  have hg : ∀ k, k ∉ ({i} : Finset (Fin n)) → Function.update y i b k = z k := by
    intro k hk
    have hki : k ≠ i := by simpa [Finset.mem_singleton] using hk
    rw [Function.update_of_ne hki]
    exact h k hk
  rw [shiUn_a1_entry, if_pos hg, Function.update_self]

private lemma shiUn_apply1Matrix {n : ℕ} (U : Matrix Bool Bool ℂ) (i : Fin n)
    (hU : star U * U = (1 : Matrix Bool Bool ℂ)) :
    star (apply1Matrix U i) * apply1Matrix U i = (1 : Op n) := by
  ext y z
  rw [Matrix.mul_apply]
  first
  | (simp only [Matrix.star_apply])
  | (simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply])
  by_cases hguard : ∀ k, k ∉ ({i} : Finset (Fin n)) → y k = z k
  · have hzero : ∀ w : Bits n, w ≠ Function.update y i false →
        w ≠ Function.update y i true →
        star (apply1Matrix U i w y) * apply1Matrix U i w z = 0 := by
      intro w h0 h1
      rw [shiUn_a1_row_vanish U i w y h0 h1, star_zero, zero_mul]
    have hsum : (∑ w : Bits n, star (apply1Matrix U i w y) * apply1Matrix U i w z)
        = star (apply1Matrix U i (Function.update y i false) y)
              * apply1Matrix U i (Function.update y i false) z
            + star (apply1Matrix U i (Function.update y i true) y)
              * apply1Matrix U i (Function.update y i true) z :=
      shiUn_two_point_sum (shiUn_update_ne i y)
        (fun w => star (apply1Matrix U i w y) * apply1Matrix U i w z) hzero
    rw [hsum]
    have hyy : ∀ k, k ∉ ({i} : Finset (Fin n)) → y k = y k := fun _ _ => rfl
    rw [shiUn_a1_row_entry U i y y false hyy, shiUn_a1_row_entry U i y z false hguard,
        shiUn_a1_row_entry U i y y true hyy, shiUn_a1_row_entry U i y z true hguard]
    have hUe : star (U true (y i)) * U true (z i) + star (U false (y i)) * U false (z i)
        = (1 : Matrix Bool Bool ℂ) (y i) (z i) := by
      have h := congrFun (congrFun hU (y i)) (z i)
      rw [Matrix.mul_apply] at h
      first
      | (simp only [Matrix.star_apply] at h)
      | (simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply] at h)
      rw [Fintype.sum_bool] at h
      exact h
    rw [add_comm, hUe]
    by_cases hyz : y i = z i
    · have hyz' : y = z := by
        funext k
        by_cases hk : k = i
        · rw [hk]
          exact hyz
        · exact hguard k (by simpa [Finset.mem_singleton] using hk)
      rw [hyz, hyz', Matrix.one_apply_eq, Matrix.one_apply_eq]
    · have hne : y ≠ z := fun h => hyz (by rw [h])
      rw [Matrix.one_apply_ne hyz, Matrix.one_apply_ne hne]
  · have hall : ∀ w : Bits n,
        star (apply1Matrix U i w y) * apply1Matrix U i w z = 0 := by
      intro w
      by_cases g1 : ∀ k, k ∉ ({i} : Finset (Fin n)) → w k = y k
      · have g2 : ¬ (∀ k, k ∉ ({i} : Finset (Fin n)) → w k = z k) := by
          intro g2
          exact hguard (fun k hk => (g1 k hk).symm.trans (g2 k hk))
        rw [shiUn_a1_entry U i w z, if_neg g2, mul_zero]
      · rw [shiUn_a1_entry U i w y, if_neg g1, star_zero, zero_mul]
    have hS : (∑ w : Bits n, star (apply1Matrix U i w y) * apply1Matrix U i w z) = 0 :=
      Finset.sum_eq_zero (fun w _ => hall w)
    have hne : y ≠ z := fun h => hguard (fun k _ => by rw [h])
    rw [hS, Matrix.one_apply_ne hne]

/-! ### `cnotMatrix i j` is unitary for `i ≠ j` -/

private lemma shiUn_cnot_entry {n : ℕ} (i j : Fin n) (y z : Bits n) :
    cnotMatrix i j y z =
      if (∀ k, k ∉ ({i, j} : Finset (Fin n)) → y k = z k) ∧ z i = y i
          ∧ z j = xor (y j) (y i) then 1 else 0 := by
  first
  | rfl
  | (simp only [cnotMatrix, Matrix.of_apply]; done)

private lemma shiUn_cnot_col_unique {n : ℕ} (i j : Fin n) (y z : Bits n)
    (h1 : ∀ k, k ∉ ({i, j} : Finset (Fin n)) → y k = z k)
    (h2 : z i = y i) (h3 : z j = xor (y j) (y i)) :
    z = Function.update y j (xor (y j) (y i)) := by
  funext k
  by_cases hkj : k = j
  · rw [hkj, Function.update_self]
    exact h3
  · rw [Function.update_of_ne hkj]
    by_cases hki : k = i
    · rw [hki]
      exact h2
    · refine (h1 k ?_).symm
      first
        | (simp [hki, hkj]; done)
        | (simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)

private lemma shiUn_cnot_cond {n : ℕ} (i j : Fin n) (hij : i ≠ j) (y : Bits n) :
    (∀ k, k ∉ ({i, j} : Finset (Fin n)) →
        y k = Function.update y j (xor (y j) (y i)) k)
      ∧ Function.update y j (xor (y j) (y i)) i = y i
      ∧ Function.update y j (xor (y j) (y i)) j = xor (y j) (y i) := by
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    have hkj : k ≠ j := by
      intro h
      exact hk (by simp [h])
    exact (Function.update_of_ne hkj (xor (y j) (y i)) y).symm
  · exact Function.update_of_ne hij (xor (y j) (y i)) y
  · exact Function.update_self j (xor (y j) (y i)) y

private lemma shiUn_cnot_entry_iff {n : ℕ} (i j : Fin n) (hij : i ≠ j) (y z : Bits n) :
    cnotMatrix i j y z =
      if z = Function.update y j (xor (y j) (y i)) then (1 : ℂ) else 0 := by
  rw [shiUn_cnot_entry]
  by_cases hc : (∀ k, k ∉ ({i, j} : Finset (Fin n)) → y k = z k) ∧ z i = y i
      ∧ z j = xor (y j) (y i)
  · rw [if_pos hc, if_pos (shiUn_cnot_col_unique i j y z hc.1 hc.2.1 hc.2.2)]
  · have hz : z ≠ Function.update y j (xor (y j) (y i)) := by
      intro hz
      exact hc (by rw [hz]; exact shiUn_cnot_cond i j hij y)
    rw [if_neg hc, if_neg hz]

private lemma shiUn_sigma_fwd {n : ℕ} (i j : Fin n) (hij : i ≠ j) (w : Bits n) :
    w = Function.update (Function.update w j (xor (w j) (w i))) j
        (xor (Function.update w j (xor (w j) (w i)) j)
             (Function.update w j (xor (w j) (w i)) i)) := by
  have hbool : ∀ a b : Bool, a = xor (xor a b) b := by decide
  funext k
  by_cases hkj : k = j
  · rw [hkj, Function.update_self, Function.update_self, Function.update_of_ne hij]
    exact hbool (w j) (w i)
  · rw [Function.update_of_ne hkj, Function.update_of_ne hkj]

private lemma shiUn_sigma_iff {n : ℕ} (i j : Fin n) (hij : i ≠ j) (w y : Bits n) :
    y = Function.update w j (xor (w j) (w i)) ↔
      w = Function.update y j (xor (y j) (y i)) := by
  constructor
  · intro h
    subst h
    exact shiUn_sigma_fwd i j hij w
  · intro h
    subst h
    exact shiUn_sigma_fwd i j hij y

private lemma shiUn_cnotMatrix {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    star (cnotMatrix i j) * cnotMatrix i j = (1 : Op n) := by
  ext y z
  rw [Matrix.mul_apply]
  first
  | (simp only [Matrix.star_apply])
  | (simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply])
  have hstar1 : ∀ w : Bits n, star (cnotMatrix i j w y)
      = if w = Function.update y j (xor (y j) (y i)) then (1 : ℂ) else 0 := by
    intro w
    rw [shiUn_cnot_entry_iff i j hij w y,
        if_congr (shiUn_sigma_iff i j hij w y) rfl rfl]
    by_cases h1 : w = Function.update y j (xor (y j) (y i))
    · rw [if_pos h1, star_one]
    · rw [if_neg h1, star_zero]
  have hval2 : ∀ w : Bits n, cnotMatrix i j w z
      = if w = Function.update z j (xor (z j) (z i)) then (1 : ℂ) else 0 := by
    intro w
    rw [shiUn_cnot_entry_iff i j hij w z,
        if_congr (shiUn_sigma_iff i j hij w z) rfl rfl]
  have hkey : ∀ w : Bits n, star (cnotMatrix i j w y) * cnotMatrix i j w z
      = (if w = Function.update y j (xor (y j) (y i)) then (1 : ℂ) else 0)
        * (if w = Function.update z j (xor (z j) (z i)) then (1 : ℂ) else 0) := by
    intro w
    rw [hstar1 w, hval2 w]
  have hS : (∑ w : Bits n, star (cnotMatrix i j w y) * cnotMatrix i j w z)
      = ∑ w : Bits n, (if w = Function.update y j (xor (y j) (y i)) then (1 : ℂ) else 0)
          * (if w = Function.update z j (xor (z j) (z i)) then (1 : ℂ) else 0) :=
    Finset.sum_congr rfl (fun w _ => hkey w)
  have h0 : ∀ w ∈ (Finset.univ : Finset (Bits n)),
      w ≠ Function.update y j (xor (y j) (y i)) →
      (if w = Function.update y j (xor (y j) (y i)) then (1 : ℂ) else 0)
        * (if w = Function.update z j (xor (z j) (z i)) then (1 : ℂ) else 0) = 0 := by
    intro w _ hw
    rw [if_neg hw, zero_mul]
  rw [hS, Finset.sum_eq_single_of_mem _ (Finset.mem_univ _) h0, if_pos rfl, one_mul]
  by_cases hyz : y = z
  · subst hyz
    rw [if_pos rfl, Matrix.one_apply_eq]
  · have hne : Function.update y j (xor (y j) (y i))
        ≠ Function.update z j (xor (z j) (z i)) := by
      intro h
      refine hyz ?_
      have h2 : y = Function.update (Function.update z j (xor (z j) (z i))) j
          (xor (Function.update z j (xor (z j) (z i)) j)
               (Function.update z j (xor (z j) (z i)) i)) :=
        (shiUn_sigma_iff i j hij (Function.update z j (xor (z j) (z i))) y).mpr h.symm
      exact h2.trans (shiUn_sigma_fwd i j hij z).symm
    rw [if_neg hne, Matrix.one_apply_ne hyz]

/-! ### Gates and layers -/

private lemma shiUn_gateMatrix {n : ℕ} (g : Instr n) :
    star (gateMatrix g) * gateMatrix g = (1 : Op n) := by
  cases g with
  | h i => exact shiUn_apply1Matrix hMat i shiUn_hMat
  | s i => exact shiUn_apply1Matrix sMat i shiUn_sMat
  | t i => exact shiUn_apply1Matrix tMat i shiUn_tMat
  | x i => exact shiUn_apply1Matrix xMat i shiUn_xMat
  | cnot i j hij => exact shiUn_cnotMatrix i j hij

private lemma shiUn_layerMatrix {n : ℕ} (l : List (Instr n)) :
    star (layerMatrix l) * layerMatrix l = (1 : Op n) := by
  induction l with
  | nil =>
      have h0 : layerMatrix ([] : List (Instr n)) = (1 : Op n) := by
        first
        | rfl
        | (simp only [layerMatrix]; done)
      rw [h0, star_one, one_mul]
  | cons g t ih =>
      have h1 : layerMatrix (g :: t) = layerMatrix t * gateMatrix g := by
        first
        | rfl
        | (simp only [layerMatrix]; done)
      rw [h1, star_mul, mul_assoc, ← mul_assoc (star (layerMatrix t)), ih, one_mul,
          shiUn_gateMatrix g]

private lemma shiUn_circMatrix {n : ℕ} (c : Layered n) :
    star (circMatrix c) * circMatrix c = (1 : Op n) := by
  induction c with
  | nil =>
      have h0 : circMatrix ([] : Layered n) = (1 : Op n) := by
        first
        | rfl
        | (simp only [circMatrix]; done)
      rw [h0, star_one, one_mul]
  | cons l t ih =>
      have h1 : circMatrix (l :: t) = circMatrix t * layerMatrix l := by
        first
        | rfl
        | (simp only [circMatrix]; done)
      rw [h1, star_mul, mul_assoc, ← mul_assoc (star (circMatrix t)), ih, one_mul,
          shiUn_layerMatrix l]

/-! ### The registered statement -/

theorem solution {n : ℕ} (c : Layered n) :
    star (circMatrix c) * circMatrix c = (1 : Op n) :=
  shiUn_circMatrix c
