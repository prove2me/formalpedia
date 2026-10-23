-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P23.ideal_choi_matrices
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T20:42:18.117779+00:00
-- url     : https://prove2.me/submissions/b2913c5e-c406-45cc-be1b-89e1816fa304

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P23

noncomputable section
namespace X7S
open QAlgorithms
open scoped Matrix
open QAlgorithms.Papers.Independent.Gap48.P23
open QAlgorithms.Papers.Independent.Information100.P58 (Word)
open QAlgorithms.Papers.Independent.Information100.P21 (Op)
open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

lemma X7_sum_pi_succ {n : ℕ} (f : (Fin (n+1) → Fin 2) → ℂ) :
    ∑ i, f i = ∑ a : Fin 2, ∑ t : Fin n → Fin 2, f (Matrix.vecCons a t) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.consEquiv fun _ => Fin 2) _ _ (fun _ => rfl)).symm

lemma X7_sum_pi_zero (f : (Fin 0 → Fin 2) → ℂ) : ∑ i, f i = f ![] := by
  rw [Fintype.sum_unique]; congr 1

def rho3 (A B C : Matrix (Fin 2) (Fin 2) ℂ) : Op (Word 3 2) :=
  fun i j => A (i 0) (j 0) * B (i 1) (j 1) * C (i 2) (j 2)

def X7P (α β γ : ℂ) : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![!![α, β; γ, 1 - α], !![1 - α, -β; -γ, α]]


lemma X7_bw3 (a b c : Fin 2) : booleanWordWeight ![a, b, c] = a.val + b.val + c.val := by
  unfold booleanWordWeight
  rw [Finset.card_eq_sum_ones, Finset.sum_filter, Fin.sum_univ_three]
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp

lemma X7_bw1 (a : Fin 2) : booleanWordWeight ![a] = a.val := by
  unfold booleanWordWeight
  rw [Finset.card_eq_sum_ones, Finset.sum_filter, Fin.sum_univ_one]
  fin_cases a <;> simp

def rho1 (A : Matrix (Fin 2) (Fin 2) ℂ) : Op (Word 1 2) :=
  fun i j => A (i 0) (j 0)

lemma X7_core1 (m : Fin 2) (a : Fin 2) (α β γ : ℂ) :
    appendixOneChannel true m (rho1 (X7P α β γ a)) =
      X7P α β γ (tableFunction 1 m.val ![a]) := by
  have e : ∀ m a : Fin 2, tableFunction 1 m.val ![a] = if m = a then 0 else 1 := by
    intro m a
    fin_cases m <;> fin_cases a <;>
      simp [tableFunction, X7_bw1]
  rw [e]
  ext i j
  fin_cases m <;> fin_cases a <;> fin_cases i <;> fin_cases j <;>
    simp [appendixOneChannel, ofChoi, rho1, X7_sum_pi_succ, X7_sum_pi_zero, Fin.sum_univ_two,
      flatOne, idealChoiID, optimalChoiID, idealChoiNOT, X7P] <;> ring

lemma X7_g3_0_00 (A B C : Matrix (Fin 2) (Fin 2) ℂ) :
    appendixThreeChannel true 0 (rho3 A B C) 0 0 =
      (1:ℂ) * (A 0 0 * B 0 0 * C 0 0) +
      (1:ℂ) * (A 0 0 * B 0 0 * C 1 1) +
      (-1/6:ℂ) * (A 0 0 * B 0 1 * C 1 0) +
      (-1/6:ℂ) * (A 0 1 * B 0 0 * C 1 0) +
      (-1/6:ℂ) * (A 0 0 * B 1 0 * C 0 1) +
      (1:ℂ) * (A 0 0 * B 1 1 * C 0 0) +
      (-1/6:ℂ) * (A 0 1 * B 1 0 * C 0 0) +
      (1/6:ℂ) * (A 0 1 * B 1 0 * C 1 1) +
      (1/6:ℂ) * (A 0 1 * B 1 1 * C 1 0) +
      (-1/6:ℂ) * (A 1 0 * B 0 0 * C 0 1) +
      (-1/6:ℂ) * (A 1 0 * B 0 1 * C 0 0) +
      (1:ℂ) * (A 1 1 * B 0 0 * C 0 0) +
      (1/6:ℂ) * (A 1 0 * B 0 1 * C 1 1) +
      (1/6:ℂ) * (A 1 1 * B 0 1 * C 1 0) +
      (1/6:ℂ) * (A 1 0 * B 1 1 * C 0 1) +
      (1/6:ℂ) * (A 1 1 * B 1 0 * C 0 1) := by
  simp [appendixThreeChannel, ofChoi, rho3, X7_sum_pi_succ, X7_sum_pi_zero, Fin.sum_univ_two,
      flatThree, idealChoiMAJ3, appendixMatrixLayout]
  ring

lemma X7_g3_0_01 (A B C : Matrix (Fin 2) (Fin 2) ℂ) :
    appendixThreeChannel true 0 (rho3 A B C) 0 1 =
      (1/3:ℂ) * (A 0 0 * B 0 0 * C 0 1) +
      (1/3:ℂ) * (A 0 0 * B 0 1 * C 0 0) +
      (1/3:ℂ) * (A 0 1 * B 0 0 * C 0 0) +
      (2/3:ℂ) * (A 0 0 * B 0 1 * C 1 1) +
      (2/3:ℂ) * (A 0 1 * B 0 0 * C 1 1) +
      (-2/3:ℂ) * (A 0 1 * B 0 1 * C 1 0) +
      (2/3:ℂ) * (A 0 0 * B 1 1 * C 0 1) +
      (-2/3:ℂ) * (A 0 1 * B 1 0 * C 0 1) +
      (2/3:ℂ) * (A 0 1 * B 1 1 * C 0 0) +
      (1/3:ℂ) * (A 0 1 * B 1 1 * C 1 1) +
      (-2/3:ℂ) * (A 1 0 * B 0 1 * C 0 1) +
      (2/3:ℂ) * (A 1 1 * B 0 0 * C 0 1) +
      (2/3:ℂ) * (A 1 1 * B 0 1 * C 0 0) +
      (1/3:ℂ) * (A 1 1 * B 0 1 * C 1 1) +
      (1/3:ℂ) * (A 1 1 * B 1 1 * C 0 1) := by
  simp [appendixThreeChannel, ofChoi, rho3, X7_sum_pi_succ, X7_sum_pi_zero, Fin.sum_univ_two,
      flatThree, idealChoiMAJ3, appendixMatrixLayout]
  ring

lemma X7_g3_0_10 (A B C : Matrix (Fin 2) (Fin 2) ℂ) :
    appendixThreeChannel true 0 (rho3 A B C) 1 0 =
      (1/3:ℂ) * (A 0 0 * B 0 0 * C 1 0) +
      (1/3:ℂ) * (A 0 0 * B 1 0 * C 0 0) +
      (2/3:ℂ) * (A 0 0 * B 1 0 * C 1 1) +
      (2/3:ℂ) * (A 0 0 * B 1 1 * C 1 0) +
      (-2/3:ℂ) * (A 0 1 * B 1 0 * C 1 0) +
      (1/3:ℂ) * (A 1 0 * B 0 0 * C 0 0) +
      (2/3:ℂ) * (A 1 0 * B 0 0 * C 1 1) +
      (-2/3:ℂ) * (A 1 0 * B 0 1 * C 1 0) +
      (2/3:ℂ) * (A 1 1 * B 0 0 * C 1 0) +
      (-2/3:ℂ) * (A 1 0 * B 1 0 * C 0 1) +
      (2/3:ℂ) * (A 1 0 * B 1 1 * C 0 0) +
      (2/3:ℂ) * (A 1 1 * B 1 0 * C 0 0) +
      (1/3:ℂ) * (A 1 0 * B 1 1 * C 1 1) +
      (1/3:ℂ) * (A 1 1 * B 1 0 * C 1 1) +
      (1/3:ℂ) * (A 1 1 * B 1 1 * C 1 0) := by
  simp [appendixThreeChannel, ofChoi, rho3, X7_sum_pi_succ, X7_sum_pi_zero, Fin.sum_univ_two,
      flatThree, idealChoiMAJ3, appendixMatrixLayout]
  ring

lemma X7_g3_0_11 (A B C : Matrix (Fin 2) (Fin 2) ℂ) :
    appendixThreeChannel true 0 (rho3 A B C) 1 1 =
      (1/6:ℂ) * (A 0 0 * B 0 1 * C 1 0) +
      (1/6:ℂ) * (A 0 1 * B 0 0 * C 1 0) +
      (1/6:ℂ) * (A 0 0 * B 1 0 * C 0 1) +
      (1/6:ℂ) * (A 0 1 * B 1 0 * C 0 0) +
      (1:ℂ) * (A 0 0 * B 1 1 * C 1 1) +
      (-1/6:ℂ) * (A 0 1 * B 1 0 * C 1 1) +
      (-1/6:ℂ) * (A 0 1 * B 1 1 * C 1 0) +
      (1/6:ℂ) * (A 1 0 * B 0 0 * C 0 1) +
      (1/6:ℂ) * (A 1 0 * B 0 1 * C 0 0) +
      (-1/6:ℂ) * (A 1 0 * B 0 1 * C 1 1) +
      (1:ℂ) * (A 1 1 * B 0 0 * C 1 1) +
      (-1/6:ℂ) * (A 1 1 * B 0 1 * C 1 0) +
      (-1/6:ℂ) * (A 1 0 * B 1 1 * C 0 1) +
      (-1/6:ℂ) * (A 1 1 * B 1 0 * C 0 1) +
      (1:ℂ) * (A 1 1 * B 1 1 * C 0 0) +
      (1:ℂ) * (A 1 1 * B 1 1 * C 1 1) := by
  simp [appendixThreeChannel, ofChoi, rho3, X7_sum_pi_succ, X7_sum_pi_zero, Fin.sum_univ_two,
      flatThree, idealChoiMAJ3, appendixMatrixLayout]
  ring

lemma X7_g3_1_00 (A B C : Matrix (Fin 2) (Fin 2) ℂ) :
    appendixThreeChannel true 1 (rho3 A B C) 0 0 =
      (1:ℂ) * (A 0 0 * B 0 0 * C 0 0) +
      (1/3:ℂ) * (A 0 0 * B 0 1 * C 1 0) +
      (1/3:ℂ) * (A 0 1 * B 0 0 * C 1 0) +
      (1/3:ℂ) * (A 0 0 * B 1 0 * C 0 1) +
      (1/3:ℂ) * (A 0 1 * B 1 0 * C 0 0) +
      (1:ℂ) * (A 0 0 * B 1 1 * C 1 1) +
      (-1/3:ℂ) * (A 0 1 * B 1 0 * C 1 1) +
      (-1/3:ℂ) * (A 0 1 * B 1 1 * C 1 0) +
      (1/3:ℂ) * (A 1 0 * B 0 0 * C 0 1) +
      (1/3:ℂ) * (A 1 0 * B 0 1 * C 0 0) +
      (-1/3:ℂ) * (A 1 0 * B 0 1 * C 1 1) +
      (1:ℂ) * (A 1 1 * B 0 0 * C 1 1) +
      (-1/3:ℂ) * (A 1 1 * B 0 1 * C 1 0) +
      (-1/3:ℂ) * (A 1 0 * B 1 1 * C 0 1) +
      (-1/3:ℂ) * (A 1 1 * B 1 0 * C 0 1) +
      (1:ℂ) * (A 1 1 * B 1 1 * C 0 0) := by
  simp [appendixThreeChannel, ofChoi, rho3, X7_sum_pi_succ, X7_sum_pi_zero, Fin.sum_univ_two,
      flatThree, idealChoiPAR3, appendixMatrixLayout]
  ring

lemma X7_g3_1_01 (A B C : Matrix (Fin 2) (Fin 2) ℂ) :
    appendixThreeChannel true 1 (rho3 A B C) 0 1 =
      (1/3:ℂ) * (A 0 0 * B 0 0 * C 0 1) +
      (1/3:ℂ) * (A 0 0 * B 0 1 * C 0 0) +
      (1/3:ℂ) * (A 0 1 * B 0 0 * C 0 0) +
      (-1/3:ℂ) * (A 0 0 * B 0 1 * C 1 1) +
      (-1/3:ℂ) * (A 0 1 * B 0 0 * C 1 1) +
      (4/3:ℂ) * (A 0 1 * B 0 1 * C 1 0) +
      (-1/3:ℂ) * (A 0 0 * B 1 1 * C 0 1) +
      (4/3:ℂ) * (A 0 1 * B 1 0 * C 0 1) +
      (-1/3:ℂ) * (A 0 1 * B 1 1 * C 0 0) +
      (1/3:ℂ) * (A 0 1 * B 1 1 * C 1 1) +
      (4/3:ℂ) * (A 1 0 * B 0 1 * C 0 1) +
      (-1/3:ℂ) * (A 1 1 * B 0 0 * C 0 1) +
      (-1/3:ℂ) * (A 1 1 * B 0 1 * C 0 0) +
      (1/3:ℂ) * (A 1 1 * B 0 1 * C 1 1) +
      (1/3:ℂ) * (A 1 1 * B 1 1 * C 0 1) := by
  simp [appendixThreeChannel, ofChoi, rho3, X7_sum_pi_succ, X7_sum_pi_zero, Fin.sum_univ_two,
      flatThree, idealChoiPAR3, appendixMatrixLayout]
  ring

lemma X7_g3_1_10 (A B C : Matrix (Fin 2) (Fin 2) ℂ) :
    appendixThreeChannel true 1 (rho3 A B C) 1 0 =
      (1/3:ℂ) * (A 0 0 * B 0 0 * C 1 0) +
      (1/3:ℂ) * (A 0 0 * B 1 0 * C 0 0) +
      (-1/3:ℂ) * (A 0 0 * B 1 0 * C 1 1) +
      (-1/3:ℂ) * (A 0 0 * B 1 1 * C 1 0) +
      (4/3:ℂ) * (A 0 1 * B 1 0 * C 1 0) +
      (1/3:ℂ) * (A 1 0 * B 0 0 * C 0 0) +
      (-1/3:ℂ) * (A 1 0 * B 0 0 * C 1 1) +
      (4/3:ℂ) * (A 1 0 * B 0 1 * C 1 0) +
      (-1/3:ℂ) * (A 1 1 * B 0 0 * C 1 0) +
      (4/3:ℂ) * (A 1 0 * B 1 0 * C 0 1) +
      (-1/3:ℂ) * (A 1 0 * B 1 1 * C 0 0) +
      (-1/3:ℂ) * (A 1 1 * B 1 0 * C 0 0) +
      (1/3:ℂ) * (A 1 0 * B 1 1 * C 1 1) +
      (1/3:ℂ) * (A 1 1 * B 1 0 * C 1 1) +
      (1/3:ℂ) * (A 1 1 * B 1 1 * C 1 0) := by
  simp [appendixThreeChannel, ofChoi, rho3, X7_sum_pi_succ, X7_sum_pi_zero, Fin.sum_univ_two,
      flatThree, idealChoiPAR3, appendixMatrixLayout]
  ring

lemma X7_g3_1_11 (A B C : Matrix (Fin 2) (Fin 2) ℂ) :
    appendixThreeChannel true 1 (rho3 A B C) 1 1 =
      (1:ℂ) * (A 0 0 * B 0 0 * C 1 1) +
      (-1/3:ℂ) * (A 0 0 * B 0 1 * C 1 0) +
      (-1/3:ℂ) * (A 0 1 * B 0 0 * C 1 0) +
      (-1/3:ℂ) * (A 0 0 * B 1 0 * C 0 1) +
      (1:ℂ) * (A 0 0 * B 1 1 * C 0 0) +
      (-1/3:ℂ) * (A 0 1 * B 1 0 * C 0 0) +
      (1/3:ℂ) * (A 0 1 * B 1 0 * C 1 1) +
      (1/3:ℂ) * (A 0 1 * B 1 1 * C 1 0) +
      (-1/3:ℂ) * (A 1 0 * B 0 0 * C 0 1) +
      (-1/3:ℂ) * (A 1 0 * B 0 1 * C 0 0) +
      (1:ℂ) * (A 1 1 * B 0 0 * C 0 0) +
      (1/3:ℂ) * (A 1 0 * B 0 1 * C 1 1) +
      (1/3:ℂ) * (A 1 1 * B 0 1 * C 1 0) +
      (1/3:ℂ) * (A 1 0 * B 1 1 * C 0 1) +
      (1/3:ℂ) * (A 1 1 * B 1 0 * C 0 1) +
      (1:ℂ) * (A 1 1 * B 1 1 * C 1 1) := by
  simp [appendixThreeChannel, ofChoi, rho3, X7_sum_pi_succ, X7_sum_pi_zero, Fin.sum_univ_two,
      flatThree, idealChoiPAR3, appendixMatrixLayout]
  ring

lemma X7_g3_2_00 (A B C : Matrix (Fin 2) (Fin 2) ℂ) :
    appendixThreeChannel true 2 (rho3 A B C) 0 0 =
      (1:ℂ) * (A 0 0 * B 0 0 * C 1 1) +
      (-1/3:ℂ) * (A 0 0 * B 0 1 * C 1 0) +
      (-1/3:ℂ) * (A 0 1 * B 0 0 * C 1 0) +
      (-1/3:ℂ) * (A 0 0 * B 1 0 * C 0 1) +
      (1:ℂ) * (A 0 0 * B 1 1 * C 0 0) +
      (-1/3:ℂ) * (A 0 1 * B 1 0 * C 0 0) +
      (1/3:ℂ) * (A 0 1 * B 1 0 * C 1 1) +
      (1/3:ℂ) * (A 0 1 * B 1 1 * C 1 0) +
      (-1/3:ℂ) * (A 1 0 * B 0 0 * C 0 1) +
      (-1/3:ℂ) * (A 1 0 * B 0 1 * C 0 0) +
      (1:ℂ) * (A 1 1 * B 0 0 * C 0 0) +
      (1/3:ℂ) * (A 1 0 * B 0 1 * C 1 1) +
      (1/3:ℂ) * (A 1 1 * B 0 1 * C 1 0) +
      (1/3:ℂ) * (A 1 0 * B 1 1 * C 0 1) +
      (1/3:ℂ) * (A 1 1 * B 1 0 * C 0 1) +
      (1:ℂ) * (A 1 1 * B 1 1 * C 1 1) := by
  simp [appendixThreeChannel, ofChoi, rho3, X7_sum_pi_succ, X7_sum_pi_zero, Fin.sum_univ_two,
      flatThree, idealChoiNPAR3, appendixMatrixLayout]
  ring

lemma X7_g3_2_01 (A B C : Matrix (Fin 2) (Fin 2) ℂ) :
    appendixThreeChannel true 2 (rho3 A B C) 0 1 =
      (-1/3:ℂ) * (A 0 0 * B 0 0 * C 0 1) +
      (-1/3:ℂ) * (A 0 0 * B 0 1 * C 0 0) +
      (-1/3:ℂ) * (A 0 1 * B 0 0 * C 0 0) +
      (1/3:ℂ) * (A 0 0 * B 0 1 * C 1 1) +
      (1/3:ℂ) * (A 0 1 * B 0 0 * C 1 1) +
      (-4/3:ℂ) * (A 0 1 * B 0 1 * C 1 0) +
      (1/3:ℂ) * (A 0 0 * B 1 1 * C 0 1) +
      (-4/3:ℂ) * (A 0 1 * B 1 0 * C 0 1) +
      (1/3:ℂ) * (A 0 1 * B 1 1 * C 0 0) +
      (-1/3:ℂ) * (A 0 1 * B 1 1 * C 1 1) +
      (-4/3:ℂ) * (A 1 0 * B 0 1 * C 0 1) +
      (1/3:ℂ) * (A 1 1 * B 0 0 * C 0 1) +
      (1/3:ℂ) * (A 1 1 * B 0 1 * C 0 0) +
      (-1/3:ℂ) * (A 1 1 * B 0 1 * C 1 1) +
      (-1/3:ℂ) * (A 1 1 * B 1 1 * C 0 1) := by
  simp [appendixThreeChannel, ofChoi, rho3, X7_sum_pi_succ, X7_sum_pi_zero, Fin.sum_univ_two,
      flatThree, idealChoiNPAR3, appendixMatrixLayout]
  ring

lemma X7_g3_2_10 (A B C : Matrix (Fin 2) (Fin 2) ℂ) :
    appendixThreeChannel true 2 (rho3 A B C) 1 0 =
      (-1/3:ℂ) * (A 0 0 * B 0 0 * C 1 0) +
      (-1/3:ℂ) * (A 0 0 * B 1 0 * C 0 0) +
      (1/3:ℂ) * (A 0 0 * B 1 0 * C 1 1) +
      (1/3:ℂ) * (A 0 0 * B 1 1 * C 1 0) +
      (-4/3:ℂ) * (A 0 1 * B 1 0 * C 1 0) +
      (-1/3:ℂ) * (A 1 0 * B 0 0 * C 0 0) +
      (1/3:ℂ) * (A 1 0 * B 0 0 * C 1 1) +
      (-4/3:ℂ) * (A 1 0 * B 0 1 * C 1 0) +
      (1/3:ℂ) * (A 1 1 * B 0 0 * C 1 0) +
      (-4/3:ℂ) * (A 1 0 * B 1 0 * C 0 1) +
      (1/3:ℂ) * (A 1 0 * B 1 1 * C 0 0) +
      (1/3:ℂ) * (A 1 1 * B 1 0 * C 0 0) +
      (-1/3:ℂ) * (A 1 0 * B 1 1 * C 1 1) +
      (-1/3:ℂ) * (A 1 1 * B 1 0 * C 1 1) +
      (-1/3:ℂ) * (A 1 1 * B 1 1 * C 1 0) := by
  simp [appendixThreeChannel, ofChoi, rho3, X7_sum_pi_succ, X7_sum_pi_zero, Fin.sum_univ_two,
      flatThree, idealChoiNPAR3, appendixMatrixLayout]
  ring

lemma X7_g3_2_11 (A B C : Matrix (Fin 2) (Fin 2) ℂ) :
    appendixThreeChannel true 2 (rho3 A B C) 1 1 =
      (1:ℂ) * (A 0 0 * B 0 0 * C 0 0) +
      (1/3:ℂ) * (A 0 0 * B 0 1 * C 1 0) +
      (1/3:ℂ) * (A 0 1 * B 0 0 * C 1 0) +
      (1/3:ℂ) * (A 0 0 * B 1 0 * C 0 1) +
      (1/3:ℂ) * (A 0 1 * B 1 0 * C 0 0) +
      (1:ℂ) * (A 0 0 * B 1 1 * C 1 1) +
      (-1/3:ℂ) * (A 0 1 * B 1 0 * C 1 1) +
      (-1/3:ℂ) * (A 0 1 * B 1 1 * C 1 0) +
      (1/3:ℂ) * (A 1 0 * B 0 0 * C 0 1) +
      (1/3:ℂ) * (A 1 0 * B 0 1 * C 0 0) +
      (-1/3:ℂ) * (A 1 0 * B 0 1 * C 1 1) +
      (1:ℂ) * (A 1 1 * B 0 0 * C 1 1) +
      (-1/3:ℂ) * (A 1 1 * B 0 1 * C 1 0) +
      (-1/3:ℂ) * (A 1 0 * B 1 1 * C 0 1) +
      (-1/3:ℂ) * (A 1 1 * B 1 0 * C 0 1) +
      (1:ℂ) * (A 1 1 * B 1 1 * C 0 0) := by
  simp [appendixThreeChannel, ofChoi, rho3, X7_sum_pi_succ, X7_sum_pi_zero, Fin.sum_univ_two,
      flatThree, idealChoiNPAR3, appendixMatrixLayout]
  ring

lemma X7_g3_3_00 (A B C : Matrix (Fin 2) (Fin 2) ℂ) :
    appendixThreeChannel true 3 (rho3 A B C) 0 0 =
      (1/6:ℂ) * (A 0 0 * B 0 1 * C 1 0) +
      (1/6:ℂ) * (A 0 1 * B 0 0 * C 1 0) +
      (1/6:ℂ) * (A 0 0 * B 1 0 * C 0 1) +
      (1/6:ℂ) * (A 0 1 * B 1 0 * C 0 0) +
      (1:ℂ) * (A 0 0 * B 1 1 * C 1 1) +
      (-1/6:ℂ) * (A 0 1 * B 1 0 * C 1 1) +
      (-1/6:ℂ) * (A 0 1 * B 1 1 * C 1 0) +
      (1/6:ℂ) * (A 1 0 * B 0 0 * C 0 1) +
      (1/6:ℂ) * (A 1 0 * B 0 1 * C 0 0) +
      (-1/6:ℂ) * (A 1 0 * B 0 1 * C 1 1) +
      (1:ℂ) * (A 1 1 * B 0 0 * C 1 1) +
      (-1/6:ℂ) * (A 1 1 * B 0 1 * C 1 0) +
      (-1/6:ℂ) * (A 1 0 * B 1 1 * C 0 1) +
      (-1/6:ℂ) * (A 1 1 * B 1 0 * C 0 1) +
      (1:ℂ) * (A 1 1 * B 1 1 * C 0 0) +
      (1:ℂ) * (A 1 1 * B 1 1 * C 1 1) := by
  simp [appendixThreeChannel, ofChoi, rho3, X7_sum_pi_succ, X7_sum_pi_zero, Fin.sum_univ_two,
      flatThree, idealChoiNMAJ3, appendixMatrixLayout]
  ring

lemma X7_g3_3_01 (A B C : Matrix (Fin 2) (Fin 2) ℂ) :
    appendixThreeChannel true 3 (rho3 A B C) 0 1 =
      (-1/3:ℂ) * (A 0 0 * B 0 0 * C 0 1) +
      (-1/3:ℂ) * (A 0 0 * B 0 1 * C 0 0) +
      (-1/3:ℂ) * (A 0 1 * B 0 0 * C 0 0) +
      (-2/3:ℂ) * (A 0 0 * B 0 1 * C 1 1) +
      (-2/3:ℂ) * (A 0 1 * B 0 0 * C 1 1) +
      (2/3:ℂ) * (A 0 1 * B 0 1 * C 1 0) +
      (-2/3:ℂ) * (A 0 0 * B 1 1 * C 0 1) +
      (2/3:ℂ) * (A 0 1 * B 1 0 * C 0 1) +
      (-2/3:ℂ) * (A 0 1 * B 1 1 * C 0 0) +
      (-1/3:ℂ) * (A 0 1 * B 1 1 * C 1 1) +
      (2/3:ℂ) * (A 1 0 * B 0 1 * C 0 1) +
      (-2/3:ℂ) * (A 1 1 * B 0 0 * C 0 1) +
      (-2/3:ℂ) * (A 1 1 * B 0 1 * C 0 0) +
      (-1/3:ℂ) * (A 1 1 * B 0 1 * C 1 1) +
      (-1/3:ℂ) * (A 1 1 * B 1 1 * C 0 1) := by
  simp [appendixThreeChannel, ofChoi, rho3, X7_sum_pi_succ, X7_sum_pi_zero, Fin.sum_univ_two,
      flatThree, idealChoiNMAJ3, appendixMatrixLayout]
  ring

lemma X7_g3_3_10 (A B C : Matrix (Fin 2) (Fin 2) ℂ) :
    appendixThreeChannel true 3 (rho3 A B C) 1 0 =
      (-1/3:ℂ) * (A 0 0 * B 0 0 * C 1 0) +
      (-1/3:ℂ) * (A 0 0 * B 1 0 * C 0 0) +
      (-2/3:ℂ) * (A 0 0 * B 1 0 * C 1 1) +
      (-2/3:ℂ) * (A 0 0 * B 1 1 * C 1 0) +
      (2/3:ℂ) * (A 0 1 * B 1 0 * C 1 0) +
      (-1/3:ℂ) * (A 1 0 * B 0 0 * C 0 0) +
      (-2/3:ℂ) * (A 1 0 * B 0 0 * C 1 1) +
      (2/3:ℂ) * (A 1 0 * B 0 1 * C 1 0) +
      (-2/3:ℂ) * (A 1 1 * B 0 0 * C 1 0) +
      (2/3:ℂ) * (A 1 0 * B 1 0 * C 0 1) +
      (-2/3:ℂ) * (A 1 0 * B 1 1 * C 0 0) +
      (-2/3:ℂ) * (A 1 1 * B 1 0 * C 0 0) +
      (-1/3:ℂ) * (A 1 0 * B 1 1 * C 1 1) +
      (-1/3:ℂ) * (A 1 1 * B 1 0 * C 1 1) +
      (-1/3:ℂ) * (A 1 1 * B 1 1 * C 1 0) := by
  simp [appendixThreeChannel, ofChoi, rho3, X7_sum_pi_succ, X7_sum_pi_zero, Fin.sum_univ_two,
      flatThree, idealChoiNMAJ3, appendixMatrixLayout]
  ring

lemma X7_g3_3_11 (A B C : Matrix (Fin 2) (Fin 2) ℂ) :
    appendixThreeChannel true 3 (rho3 A B C) 1 1 =
      (1:ℂ) * (A 0 0 * B 0 0 * C 0 0) +
      (1:ℂ) * (A 0 0 * B 0 0 * C 1 1) +
      (-1/6:ℂ) * (A 0 0 * B 0 1 * C 1 0) +
      (-1/6:ℂ) * (A 0 1 * B 0 0 * C 1 0) +
      (-1/6:ℂ) * (A 0 0 * B 1 0 * C 0 1) +
      (1:ℂ) * (A 0 0 * B 1 1 * C 0 0) +
      (-1/6:ℂ) * (A 0 1 * B 1 0 * C 0 0) +
      (1/6:ℂ) * (A 0 1 * B 1 0 * C 1 1) +
      (1/6:ℂ) * (A 0 1 * B 1 1 * C 1 0) +
      (-1/6:ℂ) * (A 1 0 * B 0 0 * C 0 1) +
      (-1/6:ℂ) * (A 1 0 * B 0 1 * C 0 0) +
      (1:ℂ) * (A 1 1 * B 0 0 * C 0 0) +
      (1/6:ℂ) * (A 1 0 * B 0 1 * C 1 1) +
      (1/6:ℂ) * (A 1 1 * B 0 1 * C 1 0) +
      (1/6:ℂ) * (A 1 0 * B 1 1 * C 0 1) +
      (1/6:ℂ) * (A 1 1 * B 1 0 * C 0 1) := by
  simp [appendixThreeChannel, ofChoi, rho3, X7_sum_pi_succ, X7_sum_pi_zero, Fin.sum_univ_two,
      flatThree, idealChoiNMAJ3, appendixMatrixLayout]
  ring

lemma X7_c3_0_000 (α β γ : ℂ) (h : β * γ = α * (1 - α)) :
    appendixThreeChannel true 0 (rho3 (X7P α β γ 0) (X7P α β γ 0) (X7P α β γ 0)) = X7P α β γ 0 := by
  ext i j; revert i j; simp only [Fin.forall_fin_two]; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [X7_g3_0_00]; simp [X7P]; linear_combination ((1:ℂ) + (-2:ℂ)*α) * h
  · rw [X7_g3_0_01]; simp [X7P]; linear_combination ((-2:ℂ)*β) * h
  · rw [X7_g3_0_10]; simp [X7P]; linear_combination ((-2:ℂ)*γ) * h
  · rw [X7_g3_0_11]; simp [X7P]; linear_combination ((-1:ℂ) + (2:ℂ)*α) * h

lemma X7_c3_0_001 (α β γ : ℂ) (h : β * γ = α * (1 - α)) :
    appendixThreeChannel true 0 (rho3 (X7P α β γ 0) (X7P α β γ 0) (X7P α β γ 1)) = X7P α β γ 0 := by
  ext i j; revert i j; simp only [Fin.forall_fin_two]; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [X7_g3_0_00]; simp [X7P]; linear_combination ((-1:ℂ) + (2:ℂ)*α) * h
  · rw [X7_g3_0_01]; simp [X7P]; linear_combination ((2:ℂ)*β) * h
  · rw [X7_g3_0_10]; simp [X7P]; linear_combination ((2:ℂ)*γ) * h
  · rw [X7_g3_0_11]; simp [X7P]; linear_combination ((1:ℂ) + (-2:ℂ)*α) * h

lemma X7_c3_0_010 (α β γ : ℂ) (h : β * γ = α * (1 - α)) :
    appendixThreeChannel true 0 (rho3 (X7P α β γ 0) (X7P α β γ 1) (X7P α β γ 0)) = X7P α β γ 0 := by
  ext i j; revert i j; simp only [Fin.forall_fin_two]; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [X7_g3_0_00]; simp [X7P]; linear_combination ((-1:ℂ) + (2:ℂ)*α) * h
  · rw [X7_g3_0_01]; simp [X7P]; linear_combination ((2:ℂ)*β) * h
  · rw [X7_g3_0_10]; simp [X7P]; linear_combination ((2:ℂ)*γ) * h
  · rw [X7_g3_0_11]; simp [X7P]; linear_combination ((1:ℂ) + (-2:ℂ)*α) * h

lemma X7_c3_0_011 (α β γ : ℂ) (h : β * γ = α * (1 - α)) :
    appendixThreeChannel true 0 (rho3 (X7P α β γ 0) (X7P α β γ 1) (X7P α β γ 1)) = X7P α β γ 1 := by
  ext i j; revert i j; simp only [Fin.forall_fin_two]; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [X7_g3_0_00]; simp [X7P]; linear_combination ((1:ℂ) + (-2:ℂ)*α) * h
  · rw [X7_g3_0_01]; simp [X7P]; linear_combination ((-2:ℂ)*β) * h
  · rw [X7_g3_0_10]; simp [X7P]; linear_combination ((-2:ℂ)*γ) * h
  · rw [X7_g3_0_11]; simp [X7P]; linear_combination ((-1:ℂ) + (2:ℂ)*α) * h

lemma X7_c3_0_100 (α β γ : ℂ) (h : β * γ = α * (1 - α)) :
    appendixThreeChannel true 0 (rho3 (X7P α β γ 1) (X7P α β γ 0) (X7P α β γ 0)) = X7P α β γ 0 := by
  ext i j; revert i j; simp only [Fin.forall_fin_two]; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [X7_g3_0_00]; simp [X7P]; linear_combination ((-1:ℂ) + (2:ℂ)*α) * h
  · rw [X7_g3_0_01]; simp [X7P]; linear_combination ((2:ℂ)*β) * h
  · rw [X7_g3_0_10]; simp [X7P]; linear_combination ((2:ℂ)*γ) * h
  · rw [X7_g3_0_11]; simp [X7P]; linear_combination ((1:ℂ) + (-2:ℂ)*α) * h

lemma X7_c3_0_101 (α β γ : ℂ) (h : β * γ = α * (1 - α)) :
    appendixThreeChannel true 0 (rho3 (X7P α β γ 1) (X7P α β γ 0) (X7P α β γ 1)) = X7P α β γ 1 := by
  ext i j; revert i j; simp only [Fin.forall_fin_two]; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [X7_g3_0_00]; simp [X7P]; linear_combination ((1:ℂ) + (-2:ℂ)*α) * h
  · rw [X7_g3_0_01]; simp [X7P]; linear_combination ((-2:ℂ)*β) * h
  · rw [X7_g3_0_10]; simp [X7P]; linear_combination ((-2:ℂ)*γ) * h
  · rw [X7_g3_0_11]; simp [X7P]; linear_combination ((-1:ℂ) + (2:ℂ)*α) * h

lemma X7_c3_0_110 (α β γ : ℂ) (h : β * γ = α * (1 - α)) :
    appendixThreeChannel true 0 (rho3 (X7P α β γ 1) (X7P α β γ 1) (X7P α β γ 0)) = X7P α β γ 1 := by
  ext i j; revert i j; simp only [Fin.forall_fin_two]; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [X7_g3_0_00]; simp [X7P]; linear_combination ((1:ℂ) + (-2:ℂ)*α) * h
  · rw [X7_g3_0_01]; simp [X7P]; linear_combination ((-2:ℂ)*β) * h
  · rw [X7_g3_0_10]; simp [X7P]; linear_combination ((-2:ℂ)*γ) * h
  · rw [X7_g3_0_11]; simp [X7P]; linear_combination ((-1:ℂ) + (2:ℂ)*α) * h

lemma X7_c3_0_111 (α β γ : ℂ) (h : β * γ = α * (1 - α)) :
    appendixThreeChannel true 0 (rho3 (X7P α β γ 1) (X7P α β γ 1) (X7P α β γ 1)) = X7P α β γ 1 := by
  ext i j; revert i j; simp only [Fin.forall_fin_two]; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [X7_g3_0_00]; simp [X7P]; linear_combination ((-1:ℂ) + (2:ℂ)*α) * h
  · rw [X7_g3_0_01]; simp [X7P]; linear_combination ((2:ℂ)*β) * h
  · rw [X7_g3_0_10]; simp [X7P]; linear_combination ((2:ℂ)*γ) * h
  · rw [X7_g3_0_11]; simp [X7P]; linear_combination ((1:ℂ) + (-2:ℂ)*α) * h

lemma X7_c3_1_000 (α β γ : ℂ) (h : β * γ = α * (1 - α)) :
    appendixThreeChannel true 1 (rho3 (X7P α β γ 0) (X7P α β γ 0) (X7P α β γ 0)) = X7P α β γ 0 := by
  ext i j; revert i j; simp only [Fin.forall_fin_two]; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [X7_g3_1_00]; simp [X7P]; linear_combination ((-2:ℂ) + (4:ℂ)*α) * h
  · rw [X7_g3_1_01]; simp [X7P]; linear_combination ((4:ℂ)*β) * h
  · rw [X7_g3_1_10]; simp [X7P]; linear_combination ((4:ℂ)*γ) * h
  · rw [X7_g3_1_11]; simp [X7P]; linear_combination ((2:ℂ) + (-4:ℂ)*α) * h

lemma X7_c3_1_001 (α β γ : ℂ) (h : β * γ = α * (1 - α)) :
    appendixThreeChannel true 1 (rho3 (X7P α β γ 0) (X7P α β γ 0) (X7P α β γ 1)) = X7P α β γ 1 := by
  ext i j; revert i j; simp only [Fin.forall_fin_two]; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [X7_g3_1_00]; simp [X7P]; linear_combination ((2:ℂ) + (-4:ℂ)*α) * h
  · rw [X7_g3_1_01]; simp [X7P]; linear_combination ((-4:ℂ)*β) * h
  · rw [X7_g3_1_10]; simp [X7P]; linear_combination ((-4:ℂ)*γ) * h
  · rw [X7_g3_1_11]; simp [X7P]; linear_combination ((-2:ℂ) + (4:ℂ)*α) * h

lemma X7_c3_1_010 (α β γ : ℂ) (h : β * γ = α * (1 - α)) :
    appendixThreeChannel true 1 (rho3 (X7P α β γ 0) (X7P α β γ 1) (X7P α β γ 0)) = X7P α β γ 1 := by
  ext i j; revert i j; simp only [Fin.forall_fin_two]; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [X7_g3_1_00]; simp [X7P]; linear_combination ((2:ℂ) + (-4:ℂ)*α) * h
  · rw [X7_g3_1_01]; simp [X7P]; linear_combination ((-4:ℂ)*β) * h
  · rw [X7_g3_1_10]; simp [X7P]; linear_combination ((-4:ℂ)*γ) * h
  · rw [X7_g3_1_11]; simp [X7P]; linear_combination ((-2:ℂ) + (4:ℂ)*α) * h

lemma X7_c3_1_011 (α β γ : ℂ) (h : β * γ = α * (1 - α)) :
    appendixThreeChannel true 1 (rho3 (X7P α β γ 0) (X7P α β γ 1) (X7P α β γ 1)) = X7P α β γ 0 := by
  ext i j; revert i j; simp only [Fin.forall_fin_two]; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [X7_g3_1_00]; simp [X7P]; linear_combination ((-2:ℂ) + (4:ℂ)*α) * h
  · rw [X7_g3_1_01]; simp [X7P]; linear_combination ((4:ℂ)*β) * h
  · rw [X7_g3_1_10]; simp [X7P]; linear_combination ((4:ℂ)*γ) * h
  · rw [X7_g3_1_11]; simp [X7P]; linear_combination ((2:ℂ) + (-4:ℂ)*α) * h

lemma X7_c3_1_100 (α β γ : ℂ) (h : β * γ = α * (1 - α)) :
    appendixThreeChannel true 1 (rho3 (X7P α β γ 1) (X7P α β γ 0) (X7P α β γ 0)) = X7P α β γ 1 := by
  ext i j; revert i j; simp only [Fin.forall_fin_two]; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [X7_g3_1_00]; simp [X7P]; linear_combination ((2:ℂ) + (-4:ℂ)*α) * h
  · rw [X7_g3_1_01]; simp [X7P]; linear_combination ((-4:ℂ)*β) * h
  · rw [X7_g3_1_10]; simp [X7P]; linear_combination ((-4:ℂ)*γ) * h
  · rw [X7_g3_1_11]; simp [X7P]; linear_combination ((-2:ℂ) + (4:ℂ)*α) * h

lemma X7_c3_1_101 (α β γ : ℂ) (h : β * γ = α * (1 - α)) :
    appendixThreeChannel true 1 (rho3 (X7P α β γ 1) (X7P α β γ 0) (X7P α β γ 1)) = X7P α β γ 0 := by
  ext i j; revert i j; simp only [Fin.forall_fin_two]; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [X7_g3_1_00]; simp [X7P]; linear_combination ((-2:ℂ) + (4:ℂ)*α) * h
  · rw [X7_g3_1_01]; simp [X7P]; linear_combination ((4:ℂ)*β) * h
  · rw [X7_g3_1_10]; simp [X7P]; linear_combination ((4:ℂ)*γ) * h
  · rw [X7_g3_1_11]; simp [X7P]; linear_combination ((2:ℂ) + (-4:ℂ)*α) * h

lemma X7_c3_1_110 (α β γ : ℂ) (h : β * γ = α * (1 - α)) :
    appendixThreeChannel true 1 (rho3 (X7P α β γ 1) (X7P α β γ 1) (X7P α β γ 0)) = X7P α β γ 0 := by
  ext i j; revert i j; simp only [Fin.forall_fin_two]; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [X7_g3_1_00]; simp [X7P]; linear_combination ((-2:ℂ) + (4:ℂ)*α) * h
  · rw [X7_g3_1_01]; simp [X7P]; linear_combination ((4:ℂ)*β) * h
  · rw [X7_g3_1_10]; simp [X7P]; linear_combination ((4:ℂ)*γ) * h
  · rw [X7_g3_1_11]; simp [X7P]; linear_combination ((2:ℂ) + (-4:ℂ)*α) * h

lemma X7_c3_1_111 (α β γ : ℂ) (h : β * γ = α * (1 - α)) :
    appendixThreeChannel true 1 (rho3 (X7P α β γ 1) (X7P α β γ 1) (X7P α β γ 1)) = X7P α β γ 1 := by
  ext i j; revert i j; simp only [Fin.forall_fin_two]; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [X7_g3_1_00]; simp [X7P]; linear_combination ((2:ℂ) + (-4:ℂ)*α) * h
  · rw [X7_g3_1_01]; simp [X7P]; linear_combination ((-4:ℂ)*β) * h
  · rw [X7_g3_1_10]; simp [X7P]; linear_combination ((-4:ℂ)*γ) * h
  · rw [X7_g3_1_11]; simp [X7P]; linear_combination ((-2:ℂ) + (4:ℂ)*α) * h

lemma X7_c3_2_000 (α β γ : ℂ) (h : β * γ = α * (1 - α)) :
    appendixThreeChannel true 2 (rho3 (X7P α β γ 0) (X7P α β γ 0) (X7P α β γ 0)) = X7P α β γ 1 := by
  ext i j; revert i j; simp only [Fin.forall_fin_two]; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [X7_g3_2_00]; simp [X7P]; linear_combination ((2:ℂ) + (-4:ℂ)*α) * h
  · rw [X7_g3_2_01]; simp [X7P]; linear_combination ((-4:ℂ)*β) * h
  · rw [X7_g3_2_10]; simp [X7P]; linear_combination ((-4:ℂ)*γ) * h
  · rw [X7_g3_2_11]; simp [X7P]; linear_combination ((-2:ℂ) + (4:ℂ)*α) * h

lemma X7_c3_2_001 (α β γ : ℂ) (h : β * γ = α * (1 - α)) :
    appendixThreeChannel true 2 (rho3 (X7P α β γ 0) (X7P α β γ 0) (X7P α β γ 1)) = X7P α β γ 0 := by
  ext i j; revert i j; simp only [Fin.forall_fin_two]; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [X7_g3_2_00]; simp [X7P]; linear_combination ((-2:ℂ) + (4:ℂ)*α) * h
  · rw [X7_g3_2_01]; simp [X7P]; linear_combination ((4:ℂ)*β) * h
  · rw [X7_g3_2_10]; simp [X7P]; linear_combination ((4:ℂ)*γ) * h
  · rw [X7_g3_2_11]; simp [X7P]; linear_combination ((2:ℂ) + (-4:ℂ)*α) * h

lemma X7_c3_2_010 (α β γ : ℂ) (h : β * γ = α * (1 - α)) :
    appendixThreeChannel true 2 (rho3 (X7P α β γ 0) (X7P α β γ 1) (X7P α β γ 0)) = X7P α β γ 0 := by
  ext i j; revert i j; simp only [Fin.forall_fin_two]; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [X7_g3_2_00]; simp [X7P]; linear_combination ((-2:ℂ) + (4:ℂ)*α) * h
  · rw [X7_g3_2_01]; simp [X7P]; linear_combination ((4:ℂ)*β) * h
  · rw [X7_g3_2_10]; simp [X7P]; linear_combination ((4:ℂ)*γ) * h
  · rw [X7_g3_2_11]; simp [X7P]; linear_combination ((2:ℂ) + (-4:ℂ)*α) * h

lemma X7_c3_2_011 (α β γ : ℂ) (h : β * γ = α * (1 - α)) :
    appendixThreeChannel true 2 (rho3 (X7P α β γ 0) (X7P α β γ 1) (X7P α β γ 1)) = X7P α β γ 1 := by
  ext i j; revert i j; simp only [Fin.forall_fin_two]; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [X7_g3_2_00]; simp [X7P]; linear_combination ((2:ℂ) + (-4:ℂ)*α) * h
  · rw [X7_g3_2_01]; simp [X7P]; linear_combination ((-4:ℂ)*β) * h
  · rw [X7_g3_2_10]; simp [X7P]; linear_combination ((-4:ℂ)*γ) * h
  · rw [X7_g3_2_11]; simp [X7P]; linear_combination ((-2:ℂ) + (4:ℂ)*α) * h

lemma X7_c3_2_100 (α β γ : ℂ) (h : β * γ = α * (1 - α)) :
    appendixThreeChannel true 2 (rho3 (X7P α β γ 1) (X7P α β γ 0) (X7P α β γ 0)) = X7P α β γ 0 := by
  ext i j; revert i j; simp only [Fin.forall_fin_two]; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [X7_g3_2_00]; simp [X7P]; linear_combination ((-2:ℂ) + (4:ℂ)*α) * h
  · rw [X7_g3_2_01]; simp [X7P]; linear_combination ((4:ℂ)*β) * h
  · rw [X7_g3_2_10]; simp [X7P]; linear_combination ((4:ℂ)*γ) * h
  · rw [X7_g3_2_11]; simp [X7P]; linear_combination ((2:ℂ) + (-4:ℂ)*α) * h

lemma X7_c3_2_101 (α β γ : ℂ) (h : β * γ = α * (1 - α)) :
    appendixThreeChannel true 2 (rho3 (X7P α β γ 1) (X7P α β γ 0) (X7P α β γ 1)) = X7P α β γ 1 := by
  ext i j; revert i j; simp only [Fin.forall_fin_two]; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [X7_g3_2_00]; simp [X7P]; linear_combination ((2:ℂ) + (-4:ℂ)*α) * h
  · rw [X7_g3_2_01]; simp [X7P]; linear_combination ((-4:ℂ)*β) * h
  · rw [X7_g3_2_10]; simp [X7P]; linear_combination ((-4:ℂ)*γ) * h
  · rw [X7_g3_2_11]; simp [X7P]; linear_combination ((-2:ℂ) + (4:ℂ)*α) * h

lemma X7_c3_2_110 (α β γ : ℂ) (h : β * γ = α * (1 - α)) :
    appendixThreeChannel true 2 (rho3 (X7P α β γ 1) (X7P α β γ 1) (X7P α β γ 0)) = X7P α β γ 1 := by
  ext i j; revert i j; simp only [Fin.forall_fin_two]; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [X7_g3_2_00]; simp [X7P]; linear_combination ((2:ℂ) + (-4:ℂ)*α) * h
  · rw [X7_g3_2_01]; simp [X7P]; linear_combination ((-4:ℂ)*β) * h
  · rw [X7_g3_2_10]; simp [X7P]; linear_combination ((-4:ℂ)*γ) * h
  · rw [X7_g3_2_11]; simp [X7P]; linear_combination ((-2:ℂ) + (4:ℂ)*α) * h

lemma X7_c3_2_111 (α β γ : ℂ) (h : β * γ = α * (1 - α)) :
    appendixThreeChannel true 2 (rho3 (X7P α β γ 1) (X7P α β γ 1) (X7P α β γ 1)) = X7P α β γ 0 := by
  ext i j; revert i j; simp only [Fin.forall_fin_two]; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [X7_g3_2_00]; simp [X7P]; linear_combination ((-2:ℂ) + (4:ℂ)*α) * h
  · rw [X7_g3_2_01]; simp [X7P]; linear_combination ((4:ℂ)*β) * h
  · rw [X7_g3_2_10]; simp [X7P]; linear_combination ((4:ℂ)*γ) * h
  · rw [X7_g3_2_11]; simp [X7P]; linear_combination ((2:ℂ) + (-4:ℂ)*α) * h

lemma X7_c3_3_000 (α β γ : ℂ) (h : β * γ = α * (1 - α)) :
    appendixThreeChannel true 3 (rho3 (X7P α β γ 0) (X7P α β γ 0) (X7P α β γ 0)) = X7P α β γ 1 := by
  ext i j; revert i j; simp only [Fin.forall_fin_two]; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [X7_g3_3_00]; simp [X7P]; linear_combination ((-1:ℂ) + (2:ℂ)*α) * h
  · rw [X7_g3_3_01]; simp [X7P]; linear_combination ((2:ℂ)*β) * h
  · rw [X7_g3_3_10]; simp [X7P]; linear_combination ((2:ℂ)*γ) * h
  · rw [X7_g3_3_11]; simp [X7P]; linear_combination ((1:ℂ) + (-2:ℂ)*α) * h

lemma X7_c3_3_001 (α β γ : ℂ) (h : β * γ = α * (1 - α)) :
    appendixThreeChannel true 3 (rho3 (X7P α β γ 0) (X7P α β γ 0) (X7P α β γ 1)) = X7P α β γ 1 := by
  ext i j; revert i j; simp only [Fin.forall_fin_two]; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [X7_g3_3_00]; simp [X7P]; linear_combination ((1:ℂ) + (-2:ℂ)*α) * h
  · rw [X7_g3_3_01]; simp [X7P]; linear_combination ((-2:ℂ)*β) * h
  · rw [X7_g3_3_10]; simp [X7P]; linear_combination ((-2:ℂ)*γ) * h
  · rw [X7_g3_3_11]; simp [X7P]; linear_combination ((-1:ℂ) + (2:ℂ)*α) * h

lemma X7_c3_3_010 (α β γ : ℂ) (h : β * γ = α * (1 - α)) :
    appendixThreeChannel true 3 (rho3 (X7P α β γ 0) (X7P α β γ 1) (X7P α β γ 0)) = X7P α β γ 1 := by
  ext i j; revert i j; simp only [Fin.forall_fin_two]; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [X7_g3_3_00]; simp [X7P]; linear_combination ((1:ℂ) + (-2:ℂ)*α) * h
  · rw [X7_g3_3_01]; simp [X7P]; linear_combination ((-2:ℂ)*β) * h
  · rw [X7_g3_3_10]; simp [X7P]; linear_combination ((-2:ℂ)*γ) * h
  · rw [X7_g3_3_11]; simp [X7P]; linear_combination ((-1:ℂ) + (2:ℂ)*α) * h

lemma X7_c3_3_011 (α β γ : ℂ) (h : β * γ = α * (1 - α)) :
    appendixThreeChannel true 3 (rho3 (X7P α β γ 0) (X7P α β γ 1) (X7P α β γ 1)) = X7P α β γ 0 := by
  ext i j; revert i j; simp only [Fin.forall_fin_two]; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [X7_g3_3_00]; simp [X7P]; linear_combination ((-1:ℂ) + (2:ℂ)*α) * h
  · rw [X7_g3_3_01]; simp [X7P]; linear_combination ((2:ℂ)*β) * h
  · rw [X7_g3_3_10]; simp [X7P]; linear_combination ((2:ℂ)*γ) * h
  · rw [X7_g3_3_11]; simp [X7P]; linear_combination ((1:ℂ) + (-2:ℂ)*α) * h

lemma X7_c3_3_100 (α β γ : ℂ) (h : β * γ = α * (1 - α)) :
    appendixThreeChannel true 3 (rho3 (X7P α β γ 1) (X7P α β γ 0) (X7P α β γ 0)) = X7P α β γ 1 := by
  ext i j; revert i j; simp only [Fin.forall_fin_two]; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [X7_g3_3_00]; simp [X7P]; linear_combination ((1:ℂ) + (-2:ℂ)*α) * h
  · rw [X7_g3_3_01]; simp [X7P]; linear_combination ((-2:ℂ)*β) * h
  · rw [X7_g3_3_10]; simp [X7P]; linear_combination ((-2:ℂ)*γ) * h
  · rw [X7_g3_3_11]; simp [X7P]; linear_combination ((-1:ℂ) + (2:ℂ)*α) * h

lemma X7_c3_3_101 (α β γ : ℂ) (h : β * γ = α * (1 - α)) :
    appendixThreeChannel true 3 (rho3 (X7P α β γ 1) (X7P α β γ 0) (X7P α β γ 1)) = X7P α β γ 0 := by
  ext i j; revert i j; simp only [Fin.forall_fin_two]; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [X7_g3_3_00]; simp [X7P]; linear_combination ((-1:ℂ) + (2:ℂ)*α) * h
  · rw [X7_g3_3_01]; simp [X7P]; linear_combination ((2:ℂ)*β) * h
  · rw [X7_g3_3_10]; simp [X7P]; linear_combination ((2:ℂ)*γ) * h
  · rw [X7_g3_3_11]; simp [X7P]; linear_combination ((1:ℂ) + (-2:ℂ)*α) * h

lemma X7_c3_3_110 (α β γ : ℂ) (h : β * γ = α * (1 - α)) :
    appendixThreeChannel true 3 (rho3 (X7P α β γ 1) (X7P α β γ 1) (X7P α β γ 0)) = X7P α β γ 0 := by
  ext i j; revert i j; simp only [Fin.forall_fin_two]; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [X7_g3_3_00]; simp [X7P]; linear_combination ((-1:ℂ) + (2:ℂ)*α) * h
  · rw [X7_g3_3_01]; simp [X7P]; linear_combination ((2:ℂ)*β) * h
  · rw [X7_g3_3_10]; simp [X7P]; linear_combination ((2:ℂ)*γ) * h
  · rw [X7_g3_3_11]; simp [X7P]; linear_combination ((1:ℂ) + (-2:ℂ)*α) * h

lemma X7_c3_3_111 (α β γ : ℂ) (h : β * γ = α * (1 - α)) :
    appendixThreeChannel true 3 (rho3 (X7P α β γ 1) (X7P α β γ 1) (X7P α β γ 1)) = X7P α β γ 0 := by
  ext i j; revert i j; simp only [Fin.forall_fin_two]; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [X7_g3_3_00]; simp [X7P]; linear_combination ((1:ℂ) + (-2:ℂ)*α) * h
  · rw [X7_g3_3_01]; simp [X7P]; linear_combination ((-2:ℂ)*β) * h
  · rw [X7_g3_3_10]; simp [X7P]; linear_combination ((-2:ℂ)*γ) * h
  · rw [X7_g3_3_11]; simp [X7P]; linear_combination ((-1:ℂ) + (2:ℂ)*α) * h

lemma X7_core3 (m : Fin 4) (a b c : Fin 2) (α β γ : ℂ) (h : β * γ = α * (1 - α)) :
    appendixThreeChannel true m (rho3 (X7P α β γ a) (X7P α β γ b) (X7P α β γ c)) =
      X7P α β γ (tableFunction 3 m.val ![a, b, c]) := by
  fin_cases m <;> fin_cases a <;> fin_cases b <;> fin_cases c
  · refine (X7_c3_0_000 α β γ h).trans ?_; congr 1 <;>
      simp [tableFunction, X7_bw3]
  · refine (X7_c3_0_001 α β γ h).trans ?_; congr 1 <;>
      simp [tableFunction, X7_bw3]
  · refine (X7_c3_0_010 α β γ h).trans ?_; congr 1 <;>
      simp [tableFunction, X7_bw3]
  · refine (X7_c3_0_011 α β γ h).trans ?_; congr 1 <;>
      simp [tableFunction, X7_bw3]
  · refine (X7_c3_0_100 α β γ h).trans ?_; congr 1 <;>
      simp [tableFunction, X7_bw3]
  · refine (X7_c3_0_101 α β γ h).trans ?_; congr 1 <;>
      simp [tableFunction, X7_bw3]
  · refine (X7_c3_0_110 α β γ h).trans ?_; congr 1 <;>
      simp [tableFunction, X7_bw3]
  · refine (X7_c3_0_111 α β γ h).trans ?_; congr 1 <;>
      simp [tableFunction, X7_bw3]
  · refine (X7_c3_1_000 α β γ h).trans ?_; congr 1 <;>
      simp [tableFunction, X7_bw3]
  · refine (X7_c3_1_001 α β γ h).trans ?_; congr 1 <;>
      simp [tableFunction, X7_bw3]
  · refine (X7_c3_1_010 α β γ h).trans ?_; congr 1 <;>
      simp [tableFunction, X7_bw3]
  · refine (X7_c3_1_011 α β γ h).trans ?_; congr 1 <;>
      simp [tableFunction, X7_bw3]
  · refine (X7_c3_1_100 α β γ h).trans ?_; congr 1 <;>
      simp [tableFunction, X7_bw3]
  · refine (X7_c3_1_101 α β γ h).trans ?_; congr 1 <;>
      simp [tableFunction, X7_bw3]
  · refine (X7_c3_1_110 α β γ h).trans ?_; congr 1 <;>
      simp [tableFunction, X7_bw3]
  · refine (X7_c3_1_111 α β γ h).trans ?_; congr 1 <;>
      simp [tableFunction, X7_bw3]
  · refine (X7_c3_2_000 α β γ h).trans ?_; congr 1 <;>
      simp [tableFunction, X7_bw3]
  · refine (X7_c3_2_001 α β γ h).trans ?_; congr 1 <;>
      simp [tableFunction, X7_bw3]
  · refine (X7_c3_2_010 α β γ h).trans ?_; congr 1 <;>
      simp [tableFunction, X7_bw3]
  · refine (X7_c3_2_011 α β γ h).trans ?_; congr 1 <;>
      simp [tableFunction, X7_bw3]
  · refine (X7_c3_2_100 α β γ h).trans ?_; congr 1 <;>
      simp [tableFunction, X7_bw3]
  · refine (X7_c3_2_101 α β γ h).trans ?_; congr 1 <;>
      simp [tableFunction, X7_bw3]
  · refine (X7_c3_2_110 α β γ h).trans ?_; congr 1 <;>
      simp [tableFunction, X7_bw3]
  · refine (X7_c3_2_111 α β γ h).trans ?_; congr 1 <;>
      simp [tableFunction, X7_bw3]
  · refine (X7_c3_3_000 α β γ h).trans ?_; congr 1 <;>
      simp [tableFunction, X7_bw3]
  · refine (X7_c3_3_001 α β γ h).trans ?_; congr 1 <;>
      simp [tableFunction, X7_bw3]
  · refine (X7_c3_3_010 α β γ h).trans ?_; congr 1 <;>
      simp [tableFunction, X7_bw3]
  · refine (X7_c3_3_011 α β γ h).trans ?_; congr 1 <;>
      simp [tableFunction, X7_bw3]
  · refine (X7_c3_3_100 α β γ h).trans ?_; congr 1 <;>
      simp [tableFunction, X7_bw3]
  · refine (X7_c3_3_101 α β γ h).trans ?_; congr 1 <;>
      simp [tableFunction, X7_bw3]
  · refine (X7_c3_3_110 α β γ h).trans ?_; congr 1 <;>
      simp [tableFunction, X7_bw3]
  · refine (X7_c3_3_111 α β γ h).trans ?_; congr 1 <;>
      simp [tableFunction, X7_bw3]

lemma X7_conj_single {ι κ : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix κ ι ℂ) (x : ι) (i j : κ) :
    (A * Matrix.single x x (1:ℂ) * Aᴴ) i j = A i x * star (A j x) := by
  simp [Matrix.mul_apply, Matrix.single_apply, Matrix.conjTranspose_apply, ite_and]

lemma X7_enc_entry {n : ℕ} (U : Op (Fin 2)) (x : Word n 2) (i j : Word n 2) :
    encodedInput U x i j = ∏ t, targetDensity U (x t) (i t) (j t) := by
  simp only [encodedInput, targetDensity, conjSuperop, X7_conj_single, tensorPower]
  rw [Finset.prod_mul_distrib, star_prod]

lemma X7_target (U : Matrix.unitaryGroup (Fin 2) ℂ) :
    ∃ α β γ : ℂ, β * γ = α * (1 - α) ∧ ∀ b, targetDensity U.val b = X7P α β γ b := by
  have h1 : U.val * star U.val = 1 := Matrix.mem_unitaryGroup_iff.mp U.prop
  have h2 : star U.val * U.val = 1 := Matrix.mem_unitaryGroup_iff'.mp U.prop
  have e00 := congrFun (congrFun h1 0) 0
  have e01 := congrFun (congrFun h1 0) 1
  have e10 := congrFun (congrFun h1 1) 0
  have e11 := congrFun (congrFun h1 1) 1
  have f00 := congrFun (congrFun h2 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply] at e00 e01 e10 e11 f00
  refine ⟨U.val 0 0 * (starRingEnd ℂ) (U.val 0 0), U.val 0 0 * (starRingEnd ℂ) (U.val 1 0), U.val 1 0 * (starRingEnd ℂ) (U.val 0 0),
    ?_, ?_⟩
  · linear_combination (U.val 0 0 * (starRingEnd ℂ) (U.val 0 0)) * f00
  · intro b
    ext i j
    fin_cases b <;> fin_cases i <;> fin_cases j <;>
      simp [targetDensity, conjSuperop, Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply,
        X7P, Matrix.conjTranspose_apply] <;>
      first
      | ring1
      | linear_combination f00
      | linear_combination e00
      | linear_combination e01
      | linear_combination e10
      | linear_combination e11
      | linear_combination e00 - f00
      | linear_combination e11 - f00

lemma X7_enc3 (U : Op (Fin 2)) (a b c : Fin 2) (α β γ : ℂ)
    (hP : ∀ b, targetDensity U b = X7P α β γ b) :
    encodedInput U ![a, b, c] = rho3 (X7P α β γ a) (X7P α β γ b) (X7P α β γ c) := by
  ext i j
  rw [X7_enc_entry, Fin.prod_univ_three]
  simp [rho3, hP]

lemma X7_enc1 (U : Op (Fin 2)) (a : Fin 2) (α β γ : ℂ)
    (hP : ∀ b, targetDensity U b = X7P α β γ b) :
    encodedInput U ![a] = rho1 (X7P α β γ a) := by
  ext i j
  rw [X7_enc_entry, Fin.prod_univ_one]
  simp [rho1, hP]

end X7S


open MeasureTheory
open scoped ComplexConjugate Matrix ComplexOrder
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq
open QAlgorithms.Papers.Independent.Information100.P58 (Word)
open QAlgorithms.Papers.Independent.Information100.P21 (Op)
open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

open QAlgorithms.Papers.Independent.Gap48.P23 X7S in
theorem solution :
    (∀ (mask : Fin 2) (x : Word 1 2) (U : Matrix.unitaryGroup (Fin 2) ℂ),
      appendixOneChannel true mask (encodedInput U.val x) = targetDensity U.val (tableFunction 1 mask.val x)) ∧
    (∀ (mask : Fin 4) (x : Word 3 2) (U : Matrix.unitaryGroup (Fin 2) ℂ),
      appendixThreeChannel true mask (encodedInput U.val x) = targetDensity U.val (tableFunction 3 mask.val x)) := by
  constructor
  · intro m x U
    obtain ⟨α, β, γ, h, hP⟩ := X7_target U
    obtain ⟨a, rfl⟩ : ∃ a, x = ![a] := ⟨x 0, by ext i; fin_cases i; rfl⟩
    rw [X7_enc1 U.val a α β γ hP, hP, X7_core1]
  · intro m x U
    obtain ⟨α, β, γ, h, hP⟩ := X7_target U
    obtain ⟨a, b, c, rfl⟩ : ∃ a b c, x = ![a, b, c] :=
      ⟨x 0, x 1, x 2, by ext i; fin_cases i <;> rfl⟩
    rw [X7_enc3 U.val a b c α β γ hP, hP, X7_core3 m a b c α β γ h]
