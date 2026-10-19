-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P09.spamStability
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T23:25:25.406975+00:00
-- url     : https://prove2.me/submissions/bad42d4f-1112-47ee-a2fa-5676ff173655

import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P09_Model
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Linarith

set_option autoImplicit false
noncomputable section
open QAlgorithms QAlgorithms.ErrorMitigation
open QAlgorithms.Papers.Independent.Independent1.P09
open scoped Matrix.Norms.L2Operator NNReal

private lemma reference_input_eq : referenceInput =
    !![1,1,1,1; 0,0,1,0; 0,0,0,1; 1,-1,0,0] := by
  have hs : (Real.sqrt 2)^2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 2 ≠ 0 := by positivity
  ext a i
  fin_cases a <;> fin_cases i <;>
    norm_num [referenceInput,idealPreparation,pauliOrder,Stabilizer.Pauli.mat,
      pureDensity,ket,act,hadamard,phaseS,pauliX,pauliY,pauliZ,Matrix.mul_apply,Matrix.trace,Fintype.sum_bool,
      Complex.mul_re,Complex.mul_im,Complex.conj_re,Complex.conj_im,
      ← pow_two, hs, hn] <;> nlinarith

private lemma reference_input_unit : IsUnit referenceInput := by
  rw [reference_input_eq]
  let C : Matrix (Fin 4) (Fin 4) ℝ :=
    !![1/2,-1/2,-1/2,1/2; 1/2,-1/2,-1/2,-1/2; 0,1,0,0; 0,0,1,0]
  have hC : (!![1,1,1,1; 0,0,1,0; 0,0,0,1; 1,-1,0,0] : Matrix (Fin 4) (Fin 4) ℝ) * C = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [C,Matrix.mul_apply,Fin.sum_univ_succ]
  exact IsUnit.of_mul_eq_one C hC


private lemma norm_product (A B : Matrix (Fin 4) (Fin 4) ℝ) :
    specNorm (A*B) ≤ specNorm A * specNorm B := by
  exact norm_mul_le A B

private lemma norm_sum (A B : Matrix (Fin 4) (Fin 4) ℝ) :
    specNorm (A+B) ≤ specNorm A + specNorm B := by
  exact norm_add_le A B

private lemma norm_nonnegative (A : Matrix (Fin 4) (Fin 4) ℝ) : 0 ≤ specNorm A :=
  norm_nonneg A

private lemma local_error_bound {n : ℕ} (A : Fin n → Matrix (Fin 4) (Fin 4) ℝ)
    (R : Matrix (Fin 4) (Fin 4) ℝ) (j : Fin n) :
    specNorm (A j-R) ≤ maxLocalError A R := by
  have h := Finset.le_sup (f := fun j => Real.toNNReal (specNorm (A j-R)))
    (Finset.mem_univ j)
  exact Real.toNNReal_le_iff_le_coe.mp h

theorem solution {n : ℕ}
    (Min Mout : Fin n → Matrix (Fin 4) (Fin 4) ℝ)
    (hin : ∀ j, IsUnit (Min j)) (hout : ∀ j, IsUnit (Mout j)) :
    let ein := maxLocalError Min referenceInput
    let eout := maxLocalError Mout referenceOutput
    maxLocalError (fun _ : Fin n => referenceInput) referenceInput = 0 ∧
    maxLocalError (fun j => Mout j*Min j*referenceInput⁻¹) referenceOutput ≤
      (eout*ein + specNorm referenceInput*eout + specNorm referenceOutput*ein)*
        specNorm referenceInput⁻¹ := by
  classical
  dsimp only
  refine ⟨?_, ?_⟩
  · simp [maxLocalError, specNorm]
  let e := maxLocalError Min referenceInput
  let f := maxLocalError Mout referenceOutput
  have he : 0 ≤ e := NNReal.coe_nonneg _
  have hf : 0 ≤ f := NNReal.coe_nonneg _
  have hR : referenceInput * referenceInput⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp reference_input_unit)
  have bound (j : Fin n) :
      specNorm (Mout j*Min j*referenceInput⁻¹-referenceOutput) ≤
        (f*e + specNorm referenceInput*f + specNorm referenceOutput*e)*
          specNorm referenceInput⁻¹ := by
    let X := Min j-referenceInput
    let Y := Mout j-referenceOutput
    have hx : specNorm X ≤ e := local_error_bound Min referenceInput j
    have hy : specNorm Y ≤ f := local_error_bound Mout referenceOutput j
    have ident : Mout j*Min j*referenceInput⁻¹-referenceOutput =
        (Y*X+Y*referenceInput+referenceOutput*X)*referenceInput⁻¹ := by
      dsimp [X,Y]
      noncomm_ring [hR]
    rw [ident]
    apply (norm_product _ _).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonnegative _)
    calc
      _ ≤ specNorm (Y*X) + specNorm (Y*referenceInput) + specNorm (referenceOutput*X) :=
        (norm_sum _ _).trans (add_le_add (norm_sum _ _) le_rfl)
      _ ≤ (specNorm Y * specNorm X) + (specNorm Y * specNorm referenceInput) +
          (specNorm referenceOutput * specNorm X) := by
        exact add_le_add (add_le_add (norm_product _ _) (norm_product _ _)) (norm_product _ _)
      _ ≤ f*e + f*specNorm referenceInput + specNorm referenceOutput*e := by
        apply add_le_add
        · apply add_le_add
          · exact mul_le_mul hy hx (norm_nonnegative _) hf
          · exact mul_le_mul_of_nonneg_right hy (norm_nonnegative _)
        · exact mul_le_mul_of_nonneg_left hx (norm_nonnegative _)
      _ = _ := by ring
  have hnonneg : 0 ≤ (f*e + specNorm referenceInput*f + specNorm referenceOutput*e)*
      specNorm referenceInput⁻¹ := by
    exact mul_nonneg (add_nonneg (add_nonneg (mul_nonneg hf he)
      (mul_nonneg (norm_nonnegative _) hf)) (mul_nonneg (norm_nonnegative _) he))
      (norm_nonnegative _)
  have hs := Finset.sup_le (fun j (_ : j ∈ Finset.univ) =>
    Real.toNNReal_le_toNNReal (bound j))
  have hc := (NNReal.coe_le_coe).mpr hs
  rw [Real.coe_toNNReal _ hnonneg] at hc
  exact hc

#print axioms solution
