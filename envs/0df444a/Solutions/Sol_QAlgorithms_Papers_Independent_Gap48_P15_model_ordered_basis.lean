-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P15.model_ordered_basis
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-22T00:29:10.759436+00:00
-- url     : https://prove2.me/submissions/0db8b783-5ab3-4961-8336-db3cc88786c4

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P15

open QAlgorithms.Papers.Independent.Gap48.P15

attribute [local instance 100] LieRing.ofAssociativeRing

-- Reuse Mathlib Matrix and Matrix.single directly. Natural one-based
-- coordinates are restricted to Fin coordinates with Matrix.submatrix.

namespace MH
open Matrix
abbrev E (a b : Fin 12) : Matrix (Fin 12) (Fin 12) ℝ := Matrix.single a b 1
lemma subS (p q : ℕ) (a b : Fin 12) (ha : a.val + 1 = p) (hb : b.val + 1 = q) :
    (Matrix.single p q (1:ℝ)).submatrix (fun i : Fin 12 => i.val + 1) (fun j : Fin 12 => j.val + 1) =
      E a b := by
  ext i j
  simp only [Matrix.submatrix_apply, E, Matrix.single_apply, Fin.ext_iff]
  congr 1
  apply propext; omega
lemma s1_5 : (Matrix.single 1 5 (1:ℝ)).submatrix (fun i : Fin 12 => i.val + 1) (fun j : Fin 12 => j.val + 1) = E 0 4 := subS 1 5 0 4 rfl rfl
lemma s5_1 : (Matrix.single 5 1 (1:ℝ)).submatrix (fun i : Fin 12 => i.val + 1) (fun j : Fin 12 => j.val + 1) = E 4 0 := subS 5 1 4 0 rfl rfl
lemma s1_6 : (Matrix.single 1 6 (1:ℝ)).submatrix (fun i : Fin 12 => i.val + 1) (fun j : Fin 12 => j.val + 1) = E 0 5 := subS 1 6 0 5 rfl rfl
lemma s6_1 : (Matrix.single 6 1 (1:ℝ)).submatrix (fun i : Fin 12 => i.val + 1) (fun j : Fin 12 => j.val + 1) = E 5 0 := subS 6 1 5 0 rfl rfl
lemma s1_7 : (Matrix.single 1 7 (1:ℝ)).submatrix (fun i : Fin 12 => i.val + 1) (fun j : Fin 12 => j.val + 1) = E 0 6 := subS 1 7 0 6 rfl rfl
lemma s7_1 : (Matrix.single 7 1 (1:ℝ)).submatrix (fun i : Fin 12 => i.val + 1) (fun j : Fin 12 => j.val + 1) = E 6 0 := subS 7 1 6 0 rfl rfl
lemma s1_8 : (Matrix.single 1 8 (1:ℝ)).submatrix (fun i : Fin 12 => i.val + 1) (fun j : Fin 12 => j.val + 1) = E 0 7 := subS 1 8 0 7 rfl rfl
lemma s8_1 : (Matrix.single 8 1 (1:ℝ)).submatrix (fun i : Fin 12 => i.val + 1) (fun j : Fin 12 => j.val + 1) = E 7 0 := subS 8 1 7 0 rfl rfl
lemma s2_5 : (Matrix.single 2 5 (1:ℝ)).submatrix (fun i : Fin 12 => i.val + 1) (fun j : Fin 12 => j.val + 1) = E 1 4 := subS 2 5 1 4 rfl rfl
lemma s5_2 : (Matrix.single 5 2 (1:ℝ)).submatrix (fun i : Fin 12 => i.val + 1) (fun j : Fin 12 => j.val + 1) = E 4 1 := subS 5 2 4 1 rfl rfl
lemma s2_6 : (Matrix.single 2 6 (1:ℝ)).submatrix (fun i : Fin 12 => i.val + 1) (fun j : Fin 12 => j.val + 1) = E 1 5 := subS 2 6 1 5 rfl rfl
lemma s6_2 : (Matrix.single 6 2 (1:ℝ)).submatrix (fun i : Fin 12 => i.val + 1) (fun j : Fin 12 => j.val + 1) = E 5 1 := subS 6 2 5 1 rfl rfl
lemma s2_7 : (Matrix.single 2 7 (1:ℝ)).submatrix (fun i : Fin 12 => i.val + 1) (fun j : Fin 12 => j.val + 1) = E 1 6 := subS 2 7 1 6 rfl rfl
lemma s7_2 : (Matrix.single 7 2 (1:ℝ)).submatrix (fun i : Fin 12 => i.val + 1) (fun j : Fin 12 => j.val + 1) = E 6 1 := subS 7 2 6 1 rfl rfl
lemma s2_8 : (Matrix.single 2 8 (1:ℝ)).submatrix (fun i : Fin 12 => i.val + 1) (fun j : Fin 12 => j.val + 1) = E 1 7 := subS 2 8 1 7 rfl rfl
lemma s8_2 : (Matrix.single 8 2 (1:ℝ)).submatrix (fun i : Fin 12 => i.val + 1) (fun j : Fin 12 => j.val + 1) = E 7 1 := subS 8 2 7 1 rfl rfl
lemma s3_5 : (Matrix.single 3 5 (1:ℝ)).submatrix (fun i : Fin 12 => i.val + 1) (fun j : Fin 12 => j.val + 1) = E 2 4 := subS 3 5 2 4 rfl rfl
lemma s5_3 : (Matrix.single 5 3 (1:ℝ)).submatrix (fun i : Fin 12 => i.val + 1) (fun j : Fin 12 => j.val + 1) = E 4 2 := subS 5 3 4 2 rfl rfl
lemma s3_6 : (Matrix.single 3 6 (1:ℝ)).submatrix (fun i : Fin 12 => i.val + 1) (fun j : Fin 12 => j.val + 1) = E 2 5 := subS 3 6 2 5 rfl rfl
lemma s6_3 : (Matrix.single 6 3 (1:ℝ)).submatrix (fun i : Fin 12 => i.val + 1) (fun j : Fin 12 => j.val + 1) = E 5 2 := subS 6 3 5 2 rfl rfl
lemma s3_7 : (Matrix.single 3 7 (1:ℝ)).submatrix (fun i : Fin 12 => i.val + 1) (fun j : Fin 12 => j.val + 1) = E 2 6 := subS 3 7 2 6 rfl rfl
lemma s7_3 : (Matrix.single 7 3 (1:ℝ)).submatrix (fun i : Fin 12 => i.val + 1) (fun j : Fin 12 => j.val + 1) = E 6 2 := subS 7 3 6 2 rfl rfl
lemma s3_8 : (Matrix.single 3 8 (1:ℝ)).submatrix (fun i : Fin 12 => i.val + 1) (fun j : Fin 12 => j.val + 1) = E 2 7 := subS 3 8 2 7 rfl rfl
lemma s8_3 : (Matrix.single 8 3 (1:ℝ)).submatrix (fun i : Fin 12 => i.val + 1) (fun j : Fin 12 => j.val + 1) = E 7 2 := subS 8 3 7 2 rfl rfl
lemma s4_5 : (Matrix.single 4 5 (1:ℝ)).submatrix (fun i : Fin 12 => i.val + 1) (fun j : Fin 12 => j.val + 1) = E 3 4 := subS 4 5 3 4 rfl rfl
lemma s5_4 : (Matrix.single 5 4 (1:ℝ)).submatrix (fun i : Fin 12 => i.val + 1) (fun j : Fin 12 => j.val + 1) = E 4 3 := subS 5 4 4 3 rfl rfl
lemma s4_6 : (Matrix.single 4 6 (1:ℝ)).submatrix (fun i : Fin 12 => i.val + 1) (fun j : Fin 12 => j.val + 1) = E 3 5 := subS 4 6 3 5 rfl rfl
lemma s6_4 : (Matrix.single 6 4 (1:ℝ)).submatrix (fun i : Fin 12 => i.val + 1) (fun j : Fin 12 => j.val + 1) = E 5 3 := subS 6 4 5 3 rfl rfl
lemma s4_7 : (Matrix.single 4 7 (1:ℝ)).submatrix (fun i : Fin 12 => i.val + 1) (fun j : Fin 12 => j.val + 1) = E 3 6 := subS 4 7 3 6 rfl rfl
lemma s7_4 : (Matrix.single 7 4 (1:ℝ)).submatrix (fun i : Fin 12 => i.val + 1) (fun j : Fin 12 => j.val + 1) = E 6 3 := subS 7 4 6 3 rfl rfl
lemma s4_8 : (Matrix.single 4 8 (1:ℝ)).submatrix (fun i : Fin 12 => i.val + 1) (fun j : Fin 12 => j.val + 1) = E 3 7 := subS 4 8 3 7 rfl rfl
lemma s8_4 : (Matrix.single 8 4 (1:ℝ)).submatrix (fun i : Fin 12 => i.val + 1) (fun j : Fin 12 => j.val + 1) = E 7 3 := subS 8 4 7 3 rfl rfl
lemma s1_2 : (Matrix.single 1 2 (1:ℝ)).submatrix (fun i : Fin 12 => i.val + 1) (fun j : Fin 12 => j.val + 1) = E 0 1 := subS 1 2 0 1 rfl rfl
lemma s2_1 : (Matrix.single 2 1 (1:ℝ)).submatrix (fun i : Fin 12 => i.val + 1) (fun j : Fin 12 => j.val + 1) = E 1 0 := subS 2 1 1 0 rfl rfl
lemma s1_3 : (Matrix.single 1 3 (1:ℝ)).submatrix (fun i : Fin 12 => i.val + 1) (fun j : Fin 12 => j.val + 1) = E 0 2 := subS 1 3 0 2 rfl rfl
lemma s3_1 : (Matrix.single 3 1 (1:ℝ)).submatrix (fun i : Fin 12 => i.val + 1) (fun j : Fin 12 => j.val + 1) = E 2 0 := subS 3 1 2 0 rfl rfl
lemma s1_4 : (Matrix.single 1 4 (1:ℝ)).submatrix (fun i : Fin 12 => i.val + 1) (fun j : Fin 12 => j.val + 1) = E 0 3 := subS 1 4 0 3 rfl rfl
lemma s4_1 : (Matrix.single 4 1 (1:ℝ)).submatrix (fun i : Fin 12 => i.val + 1) (fun j : Fin 12 => j.val + 1) = E 3 0 := subS 4 1 3 0 rfl rfl
lemma s2_3 : (Matrix.single 2 3 (1:ℝ)).submatrix (fun i : Fin 12 => i.val + 1) (fun j : Fin 12 => j.val + 1) = E 1 2 := subS 2 3 1 2 rfl rfl
lemma s3_2 : (Matrix.single 3 2 (1:ℝ)).submatrix (fun i : Fin 12 => i.val + 1) (fun j : Fin 12 => j.val + 1) = E 2 1 := subS 3 2 2 1 rfl rfl
lemma s2_4 : (Matrix.single 2 4 (1:ℝ)).submatrix (fun i : Fin 12 => i.val + 1) (fun j : Fin 12 => j.val + 1) = E 1 3 := subS 2 4 1 3 rfl rfl
lemma s4_2 : (Matrix.single 4 2 (1:ℝ)).submatrix (fun i : Fin 12 => i.val + 1) (fun j : Fin 12 => j.val + 1) = E 3 1 := subS 4 2 3 1 rfl rfl
lemma s3_4 : (Matrix.single 3 4 (1:ℝ)).submatrix (fun i : Fin 12 => i.val + 1) (fun j : Fin 12 => j.val + 1) = E 2 3 := subS 3 4 2 3 rfl rfl
lemma s4_3 : (Matrix.single 4 3 (1:ℝ)).submatrix (fun i : Fin 12 => i.val + 1) (fun j : Fin 12 => j.val + 1) = E 3 2 := subS 4 3 3 2 rfl rfl
lemma s5_6 : (Matrix.single 5 6 (1:ℝ)).submatrix (fun i : Fin 12 => i.val + 1) (fun j : Fin 12 => j.val + 1) = E 4 5 := subS 5 6 4 5 rfl rfl
lemma s6_5 : (Matrix.single 6 5 (1:ℝ)).submatrix (fun i : Fin 12 => i.val + 1) (fun j : Fin 12 => j.val + 1) = E 5 4 := subS 6 5 5 4 rfl rfl
lemma s5_7 : (Matrix.single 5 7 (1:ℝ)).submatrix (fun i : Fin 12 => i.val + 1) (fun j : Fin 12 => j.val + 1) = E 4 6 := subS 5 7 4 6 rfl rfl
lemma s7_5 : (Matrix.single 7 5 (1:ℝ)).submatrix (fun i : Fin 12 => i.val + 1) (fun j : Fin 12 => j.val + 1) = E 6 4 := subS 7 5 6 4 rfl rfl
lemma s5_8 : (Matrix.single 5 8 (1:ℝ)).submatrix (fun i : Fin 12 => i.val + 1) (fun j : Fin 12 => j.val + 1) = E 4 7 := subS 5 8 4 7 rfl rfl
lemma s8_5 : (Matrix.single 8 5 (1:ℝ)).submatrix (fun i : Fin 12 => i.val + 1) (fun j : Fin 12 => j.val + 1) = E 7 4 := subS 8 5 7 4 rfl rfl
lemma s6_7 : (Matrix.single 6 7 (1:ℝ)).submatrix (fun i : Fin 12 => i.val + 1) (fun j : Fin 12 => j.val + 1) = E 5 6 := subS 6 7 5 6 rfl rfl
lemma s7_6 : (Matrix.single 7 6 (1:ℝ)).submatrix (fun i : Fin 12 => i.val + 1) (fun j : Fin 12 => j.val + 1) = E 6 5 := subS 7 6 6 5 rfl rfl
lemma s6_8 : (Matrix.single 6 8 (1:ℝ)).submatrix (fun i : Fin 12 => i.val + 1) (fun j : Fin 12 => j.val + 1) = E 5 7 := subS 6 8 5 7 rfl rfl
lemma s8_6 : (Matrix.single 8 6 (1:ℝ)).submatrix (fun i : Fin 12 => i.val + 1) (fun j : Fin 12 => j.val + 1) = E 7 5 := subS 8 6 7 5 rfl rfl
lemma s7_8 : (Matrix.single 7 8 (1:ℝ)).submatrix (fun i : Fin 12 => i.val + 1) (fun j : Fin 12 => j.val + 1) = E 6 7 := subS 7 8 6 7 rfl rfl
lemma s8_7 : (Matrix.single 8 7 (1:ℝ)).submatrix (fun i : Fin 12 => i.val + 1) (fun j : Fin 12 => j.val + 1) = E 7 6 := subS 8 7 7 6 rfl rfl
lemma s9_10 : (Matrix.single 9 10 (1:ℝ)).submatrix (fun i : Fin 12 => i.val + 1) (fun j : Fin 12 => j.val + 1) = E 8 9 := subS 9 10 8 9 rfl rfl
lemma s10_9 : (Matrix.single 10 9 (1:ℝ)).submatrix (fun i : Fin 12 => i.val + 1) (fun j : Fin 12 => j.val + 1) = E 9 8 := subS 10 9 9 8 rfl rfl
lemma s11_12 : (Matrix.single 11 12 (1:ℝ)).submatrix (fun i : Fin 12 => i.val + 1) (fun j : Fin 12 => j.val + 1) = E 10 11 := subS 11 12 10 11 rfl rfl
lemma s12_11 : (Matrix.single 12 11 (1:ℝ)).submatrix (fun i : Fin 12 => i.val + 1) (fun j : Fin 12 => j.val + 1) = E 11 10 := subS 12 11 11 10 rfl rfl
lemma s9_11 : (Matrix.single 9 11 (1:ℝ)).submatrix (fun i : Fin 12 => i.val + 1) (fun j : Fin 12 => j.val + 1) = E 8 10 := subS 9 11 8 10 rfl rfl
lemma s11_9 : (Matrix.single 11 9 (1:ℝ)).submatrix (fun i : Fin 12 => i.val + 1) (fun j : Fin 12 => j.val + 1) = E 10 8 := subS 11 9 10 8 rfl rfl
lemma s9_12 : (Matrix.single 9 12 (1:ℝ)).submatrix (fun i : Fin 12 => i.val + 1) (fun j : Fin 12 => j.val + 1) = E 8 11 := subS 9 12 8 11 rfl rfl
lemma s12_9 : (Matrix.single 12 9 (1:ℝ)).submatrix (fun i : Fin 12 => i.val + 1) (fun j : Fin 12 => j.val + 1) = E 11 8 := subS 12 9 11 8 rfl rfl
lemma s10_11 : (Matrix.single 10 11 (1:ℝ)).submatrix (fun i : Fin 12 => i.val + 1) (fun j : Fin 12 => j.val + 1) = E 9 10 := subS 10 11 9 10 rfl rfl
lemma s11_10 : (Matrix.single 11 10 (1:ℝ)).submatrix (fun i : Fin 12 => i.val + 1) (fun j : Fin 12 => j.val + 1) = E 10 9 := subS 11 10 10 9 rfl rfl
lemma s10_12 : (Matrix.single 10 12 (1:ℝ)).submatrix (fun i : Fin 12 => i.val + 1) (fun j : Fin 12 => j.val + 1) = E 9 11 := subS 10 12 9 11 rfl rfl
lemma s12_10 : (Matrix.single 12 10 (1:ℝ)).submatrix (fun i : Fin 12 => i.val + 1) (fun j : Fin 12 => j.val + 1) = E 11 9 := subS 12 10 11 9 rfl rfl
def b' : Fin 34 → Matrix (Fin 12) (Fin 12) ℝ := ![
  E 0 4 + E 4 0,
  E 0 5 + E 5 0,
  E 0 6 + E 6 0,
  E 0 7 + E 7 0,
  E 1 4 + E 4 1,
  E 1 5 + E 5 1,
  E 1 6 + E 6 1,
  E 1 7 + E 7 1,
  E 2 4 + E 4 2,
  E 2 5 + E 5 2,
  E 2 6 + E 6 2,
  E 2 7 + E 7 2,
  E 3 4 + E 4 3,
  E 3 5 + E 5 3,
  E 3 6 + E 6 3,
  E 3 7 + E 7 3,
  E 0 1 - E 1 0,
  E 0 2 - E 2 0,
  E 0 3 - E 3 0,
  E 1 2 - E 2 1,
  E 1 3 - E 3 1,
  E 2 3 - E 3 2,
  E 4 5 - E 5 4,
  E 4 6 - E 6 4,
  E 4 7 - E 7 4,
  E 5 6 - E 6 5,
  E 5 7 - E 7 5,
  E 6 7 - E 7 6,
  E 8 9 - E 9 8,
  E 10 11 - E 11 10,
  E 8 10 + E 10 8,
  E 8 11 + E 11 8,
  E 9 10 + E 10 9,
  E 9 11 + E 11 9]
lemma heq : modelBasis = b' := by
  funext k; fin_cases k <;>
    simp only [modelBasis, b', QAlgorithms.Papers.Independent.Gap48.P15.J, QAlgorithms.Papers.Independent.Gap48.P15.Z, s1_2, s1_3, s1_4, s1_5, s1_6, s1_7, s1_8, s2_1, s2_3, s2_4, s2_5, s2_6, s2_7, s2_8, s3_1, s3_2, s3_4, s3_5, s3_6, s3_7, s3_8, s4_1, s4_2, s4_3, s4_5, s4_6, s4_7, s4_8, s5_1, s5_2, s5_3, s5_4, s5_6, s5_7, s5_8, s6_1, s6_2, s6_3, s6_4, s6_5, s6_7, s6_8, s7_1, s7_2, s7_3, s7_4, s7_5, s7_6, s7_8, s8_1, s8_2, s8_3, s8_4, s8_5, s8_6, s8_7, s9_10, s9_11, s9_12, s10_9, s10_11, s10_12, s11_9, s11_10, s11_12, s12_9, s12_10, s12_11] <;> rfl
set_option maxHeartbeats 8000000 in
lemma lin : LinearIndependent ℝ b' := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have e : ∀ r c, (∑ i, g i • b' i) r c = 0 := fun r c => by rw [hg]; rfl
  have h0 := e 0 4
  have h1 := e 0 5
  have h2 := e 0 6
  have h3 := e 0 7
  have h4 := e 1 4
  have h5 := e 1 5
  have h6 := e 1 6
  have h7 := e 1 7
  have h8 := e 2 4
  have h9 := e 2 5
  have h10 := e 2 6
  have h11 := e 2 7
  have h12 := e 3 4
  have h13 := e 3 5
  have h14 := e 3 6
  have h15 := e 3 7
  have h16 := e 0 1
  have h17 := e 0 2
  have h18 := e 0 3
  have h19 := e 1 2
  have h20 := e 1 3
  have h21 := e 2 3
  have h22 := e 4 5
  have h23 := e 4 6
  have h24 := e 4 7
  have h25 := e 5 6
  have h26 := e 5 7
  have h27 := e 6 7
  have h28 := e 8 9
  have h29 := e 10 11
  have h30 := e 8 10
  have h31 := e 8 11
  have h32 := e 9 10
  have h33 := e 9 11
  simp only [Matrix.sum_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.smul_apply, b', E,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_one, Matrix.head_cons, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two, Matrix.cons_val, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33
  simp (config := {decide := true}) only [Matrix.single_apply, and_true, and_false, true_and, false_and,
    if_true, if_false, ite_true, ite_false, mul_zero, mul_one, zero_add, add_zero, sub_zero, zero_sub, Fin.reduceSucc] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33
  intro k; fin_cases k <;> simp only [Fin.reduceFinMk, Fin.zero_eta, Fin.mk_one] <;> linarith
def d1 : Fin 12 → ℝ := fun i => if i.val < 4 then 1 else if i.val < 8 then -1 else 0
def d2 : Fin 12 → ℝ := fun i => if i.val < 8 then 0 else if i.val < 10 then 1 else -1
lemma memP (A : Matrix (Fin 12) (Fin 12) ℝ) : A ∈ blockModel ↔
    (∀ r c, A c r * d1 c + d1 r * A r c = 0) ∧ (∀ r c, A c r * d2 c + d2 r * A r c = 0) := by
  simp only [blockModel, LieSubalgebra.mem_inf, mem_skewAdjointMatricesLieSubalgebra,
    mem_skewAdjointMatricesSubmodule, Matrix.IsSkewAdjoint, Matrix.IsAdjointPair,
    firstBlockForm, secondBlockForm]
  rw [← Matrix.ext_iff, ← Matrix.ext_iff]
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.transpose_apply, Matrix.neg_apply]
  constructor <;> rintro ⟨h1, h2⟩ <;>
    exact ⟨fun r c => by simp only [d1] at *; linarith [h1 r c], fun r c => by simp only [d2] at *; linarith [h2 r c]⟩
lemma pZ (d : Fin 12 → ℝ) (a b : Fin 12) (hab : a ≠ b) (h : d a + d b = 0) :
    ∀ r c, (E a b + E b a) c r * d c + d r * (E a b + E b a) r c = 0 := by
  intro r c
  simp only [E, Matrix.add_apply, Matrix.single_apply]
  split_ifs <;> simp_all <;> grind
lemma pJ (d : Fin 12 → ℝ) (a b : Fin 12) (hab : a ≠ b) (h : d a - d b = 0) :
    ∀ r c, (E a b - E b a) c r * d c + d r * (E a b - E b a) r c = 0 := by
  intro r c
  simp only [E, Matrix.sub_apply, Matrix.single_apply]
  split_ifs <;> simp_all <;> grind
lemma bmem : ∀ k, b' k ∈ blockModel := by
  intro k; rw [memP]; fin_cases k <;> simp only [b', Fin.reduceFinMk, Fin.zero_eta, Fin.mk_one, Matrix.cons_val]
  · exact ⟨pZ d1 0 4 (by decide) (by norm_num [d1]), pZ d2 0 4 (by decide) (by norm_num [d2])⟩
  · exact ⟨pZ d1 0 5 (by decide) (by norm_num [d1]), pZ d2 0 5 (by decide) (by norm_num [d2])⟩
  · exact ⟨pZ d1 0 6 (by decide) (by norm_num [d1]), pZ d2 0 6 (by decide) (by norm_num [d2])⟩
  · exact ⟨pZ d1 0 7 (by decide) (by norm_num [d1]), pZ d2 0 7 (by decide) (by norm_num [d2])⟩
  · exact ⟨pZ d1 1 4 (by decide) (by norm_num [d1]), pZ d2 1 4 (by decide) (by norm_num [d2])⟩
  · exact ⟨pZ d1 1 5 (by decide) (by norm_num [d1]), pZ d2 1 5 (by decide) (by norm_num [d2])⟩
  · exact ⟨pZ d1 1 6 (by decide) (by norm_num [d1]), pZ d2 1 6 (by decide) (by norm_num [d2])⟩
  · exact ⟨pZ d1 1 7 (by decide) (by norm_num [d1]), pZ d2 1 7 (by decide) (by norm_num [d2])⟩
  · exact ⟨pZ d1 2 4 (by decide) (by norm_num [d1]), pZ d2 2 4 (by decide) (by norm_num [d2])⟩
  · exact ⟨pZ d1 2 5 (by decide) (by norm_num [d1]), pZ d2 2 5 (by decide) (by norm_num [d2])⟩
  · exact ⟨pZ d1 2 6 (by decide) (by norm_num [d1]), pZ d2 2 6 (by decide) (by norm_num [d2])⟩
  · exact ⟨pZ d1 2 7 (by decide) (by norm_num [d1]), pZ d2 2 7 (by decide) (by norm_num [d2])⟩
  · exact ⟨pZ d1 3 4 (by decide) (by norm_num [d1]), pZ d2 3 4 (by decide) (by norm_num [d2])⟩
  · exact ⟨pZ d1 3 5 (by decide) (by norm_num [d1]), pZ d2 3 5 (by decide) (by norm_num [d2])⟩
  · exact ⟨pZ d1 3 6 (by decide) (by norm_num [d1]), pZ d2 3 6 (by decide) (by norm_num [d2])⟩
  · exact ⟨pZ d1 3 7 (by decide) (by norm_num [d1]), pZ d2 3 7 (by decide) (by norm_num [d2])⟩
  · exact ⟨pJ d1 0 1 (by decide) (by norm_num [d1]), pJ d2 0 1 (by decide) (by norm_num [d2])⟩
  · exact ⟨pJ d1 0 2 (by decide) (by norm_num [d1]), pJ d2 0 2 (by decide) (by norm_num [d2])⟩
  · exact ⟨pJ d1 0 3 (by decide) (by norm_num [d1]), pJ d2 0 3 (by decide) (by norm_num [d2])⟩
  · exact ⟨pJ d1 1 2 (by decide) (by norm_num [d1]), pJ d2 1 2 (by decide) (by norm_num [d2])⟩
  · exact ⟨pJ d1 1 3 (by decide) (by norm_num [d1]), pJ d2 1 3 (by decide) (by norm_num [d2])⟩
  · exact ⟨pJ d1 2 3 (by decide) (by norm_num [d1]), pJ d2 2 3 (by decide) (by norm_num [d2])⟩
  · exact ⟨pJ d1 4 5 (by decide) (by norm_num [d1]), pJ d2 4 5 (by decide) (by norm_num [d2])⟩
  · exact ⟨pJ d1 4 6 (by decide) (by norm_num [d1]), pJ d2 4 6 (by decide) (by norm_num [d2])⟩
  · exact ⟨pJ d1 4 7 (by decide) (by norm_num [d1]), pJ d2 4 7 (by decide) (by norm_num [d2])⟩
  · exact ⟨pJ d1 5 6 (by decide) (by norm_num [d1]), pJ d2 5 6 (by decide) (by norm_num [d2])⟩
  · exact ⟨pJ d1 5 7 (by decide) (by norm_num [d1]), pJ d2 5 7 (by decide) (by norm_num [d2])⟩
  · exact ⟨pJ d1 6 7 (by decide) (by norm_num [d1]), pJ d2 6 7 (by decide) (by norm_num [d2])⟩
  · exact ⟨pJ d1 8 9 (by decide) (by norm_num [d1]), pJ d2 8 9 (by decide) (by norm_num [d2])⟩
  · exact ⟨pJ d1 10 11 (by decide) (by norm_num [d1]), pJ d2 10 11 (by decide) (by norm_num [d2])⟩
  · exact ⟨pZ d1 8 10 (by decide) (by norm_num [d1]), pZ d2 8 10 (by decide) (by norm_num [d2])⟩
  · exact ⟨pZ d1 8 11 (by decide) (by norm_num [d1]), pZ d2 8 11 (by decide) (by norm_num [d2])⟩
  · exact ⟨pZ d1 9 10 (by decide) (by norm_num [d1]), pZ d2 9 10 (by decide) (by norm_num [d2])⟩
  · exact ⟨pZ d1 9 11 (by decide) (by norm_num [d1]), pZ d2 9 11 (by decide) (by norm_num [d2])⟩
def rk : Fin 34 → Fin 12 := ![0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 0, 0, 0, 1, 1, 2, 4, 4, 4, 5, 5, 6, 8, 10, 8, 8, 9, 9]
def ck : Fin 34 → Fin 12 := ![4, 5, 6, 7, 4, 5, 6, 7, 4, 5, 6, 7, 4, 5, 6, 7, 1, 2, 3, 2, 3, 3, 5, 6, 7, 6, 7, 7, 9, 11, 10, 11, 10, 11]
set_option maxHeartbeats 8000000 in
lemma decomp (A : Matrix (Fin 12) (Fin 12) ℝ) (hA : A ∈ blockModel) :
    A = ∑ k, A (rk k) (ck k) • b' k := by
  rw [memP] at hA
  obtain ⟨h1, h2⟩ := hA
  ext r c
  have a1 := h1 r c
  have a2 := h2 r c
  have a3 := h1 r r
  have a4 := h2 r r
  simp only [Matrix.sum_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.smul_apply, rk, ck, b', E,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_one, Matrix.head_cons, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Matrix.cons_val,
    Matrix.add_apply, Matrix.sub_apply, smul_eq_mul]
  fin_cases r <;> fin_cases c <;>
    simp (config := {decide := true}) only [Fin.reduceFinMk, Fin.zero_eta, Fin.mk_one, Matrix.single_apply, d1, d2, and_true, and_false, true_and, false_and, if_true, if_false, ite_true, ite_false, mul_zero, mul_one, zero_add, add_zero, one_mul, zero_mul, mul_neg, neg_mul, sub_zero, zero_sub] at a1 a2 a3 a4 ⊢ <;> linarith
end MH

/-- The literal 34-matrix family is a real basis of the block model so(4,4) plus
so(2,2). Source: PDF pp. 16-17. Both cross-block rectangles are excluded. -/
theorem solution : isBasisFor blockModel modelBasis := by
  unfold isBasisFor; rw [MH.heq]
  refine ⟨MH.lin, le_antisymm ?_ ?_⟩
  · rw [Submodule.span_le]; rintro _ ⟨k, rfl⟩; exact MH.bmem k
  · intro A hA
    rw [MH.decomp A hA]
    exact Submodule.sum_mem _ (fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))


