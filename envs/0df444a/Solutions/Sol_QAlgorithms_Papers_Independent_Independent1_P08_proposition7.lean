-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P08.proposition7
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T01:51:42.135186+00:00
-- url     : https://prove2.me/submissions/26052006-72d1-4eb9-b9ed-d3c9545afe88

import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P08_Model
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic

noncomputable section
open scoped Matrix ComplexOrder Kronecker
open QAlgorithms QAlgorithms.Entanglement QAlgorithms.QubitChannels
open QAlgorithms.Papers.Independent.Independent1.P08

@[simp] private lemma transpose_apply (X : Matrix Bool Bool ℂ) : transposeMap X = Xᵀ := rfl

private lemma cp_comp (F G : QMap) (hF : IsCompletelyPositive F)
    (hG : IsCompletelyPositive G) : IsCompletelyPositive (F.comp G) := by
  intro r X hX
  exact hF r _ (hG r X hX)

-- Transposing the entire amplified matrix reverses both the reference blocks and entries.
private lemma cp_transpose (F : QMap) (hF : IsCompletelyPositive F) :
    IsCompletelyPositive (transposeMap.comp (F.comp transposeMap)) := by
  intro r X hX
  have h := (hF r Xᵀ hX.transpose).transpose
  have he : idTensorSuperop (transposeMap.comp (F.comp transposeMap)) X =
      (idTensorSuperop F Xᵀ)ᵀ := by ext p q; rfl
  rw [he]
  exact h

private def sandwich (A : Matrix Bool Bool ℂ) : QMap where
  toFun X := A * X * Aᴴ
  map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by simp

private lemma cp_sandwich (A : Matrix Bool Bool ℂ) : IsCompletelyPositive (sandwich A) := by
  intro r X hX
  have h := hX.mul_mul_conjTranspose_same
    ((1 : Matrix (Fin r) (Fin r) ℂ) ⊗ₖ A)
  suffices he : idTensorSuperop (sandwich A) X =
      ((1 : Matrix (Fin r) (Fin r) ℂ) ⊗ₖ A) * X *
        ((1 : Matrix (Fin r) (Fin r) ℂ) ⊗ₖ A)ᴴ by
    rw [he]; exact h
  ext p q
  simp [idTensorSuperop,sandwich,Matrix.mul_apply,
    Matrix.conjTranspose_apply,Fintype.sum_prod_type,Matrix.one_apply,apply_ite,
    eq_comm]

private def A (j : Fin 3) : Matrix Bool Bool ℂ := ![pauliZ,1,pauliX] j
private def C (j : Fin 3) : QMap := sandwich (A j)
private def R (j : Fin 3) : QMap := (C j).comp transposeMap

private lemma cp_C (j : Fin 3) : IsCompletelyPositive (C j) := cp_sandwich _

private lemma C_invol (j : Fin 3) (X : Matrix Bool Bool ℂ) : C j (C j X) = X := by
  fin_cases j <;> ext i k <;> cases i <;> cases k <;>
    simp [C,A,sandwich,pauliX,pauliZ,Matrix.mul_apply,Matrix.conjTranspose_apply]

private lemma C_transpose (j : Fin 3) (X : Matrix Bool Bool ℂ) :
    C j Xᵀ = (C j X)ᵀ := by
  fin_cases j <;> ext i k <;> cases i <;> cases k <;>
    simp [C,A,sandwich,pauliX,pauliZ,Matrix.mul_apply,Matrix.conjTranspose_apply]

private lemma cp_Rsandwich (F : QMap) (hF : IsCompletelyPositive F) (j : Fin 3) :
    IsCompletelyPositive ((R j).comp (F.comp (R j))) := by
  have h := cp_comp (C j) ((transposeMap.comp (F.comp transposeMap)).comp (C j))
    (cp_C j) (cp_comp _ _ (cp_transpose F hF) (cp_C j))
  convert h using 1
  ext X i k
  change C j (F (C j Xᵀ))ᵀ i k = C j (F (C j X)ᵀ)ᵀ i k
  rw [C_transpose j X]

private lemma canonical_entries (t lam : Bloch) (X : Matrix Bool Bool ℂ) :
    canonical t lam X = Matrix.of (fun i k : Bool =>
      if i then
        (if k then (X false false+X true true)/2*(1-(t 2 : ℂ)) -
          (lam 2 : ℂ)*(X false false-X true true)/2
        else (X false false+X true true)/2*((t 0 : ℂ)+Complex.I*(t 1 : ℂ)) +
          ((lam 0 : ℂ)*(X false true+X true false)-(lam 1 : ℂ)*(X false true-X true false))/2)
      else
        (if k then (X false false+X true true)/2*((t 0 : ℂ)-Complex.I*(t 1 : ℂ)) +
          ((lam 0 : ℂ)*(X false true+X true false)+(lam 1 : ℂ)*(X false true-X true false))/2
        else (X false false+X true true)/2*(1+(t 2 : ℂ)) +
          (lam 2 : ℂ)*(X false false-X true true)/2)) := by
  ext i k
  cases i <;> cases k <;>
    simp [canonical,blochAffineMap,sigma,pauliX,pauliY,pauliZ,Matrix.mul_apply,
      Matrix.trace,Fin.sum_univ_succ,Matrix.diagonal_apply] <;> ring_nf <;> simp [Complex.I_sq] <;> ring

private lemma flip_t (t lam : Bloch) (j : Fin 3) :
    canonical (Function.update t j (-t j)) lam = (R j).comp ((canonical t lam).comp (R j)) := by
  fin_cases j <;> ext X i k <;> cases i <;> cases k <;>
    simp [R,C,A,sandwich,canonical_entries,pauliX,pauliZ,
      Matrix.mul_apply,Matrix.conjTranspose_apply,LinearMap.coe_mk,Matrix.transpose_apply] <;> ring_nf <;> simp

private lemma flip_lam (t lam : Bloch) (j : Fin 3) :
    canonical t (Function.update lam j (-lam j)) = (canonical t lam).comp (R j) := by
  fin_cases j <;> ext X i k <;> cases i <;> cases k <;>
    simp [R,C,A,sandwich,canonical_entries,pauliX,pauliZ,
      Matrix.mul_apply,Matrix.conjTranspose_apply,LinearMap.coe_mk,Matrix.transpose_apply] <;> ring_nf <;> simp

private lemma R_one : R 1 = transposeMap := by
  ext X i j
  simp [R,C,A,sandwich]

private lemma cp_right_R_iff (F : QMap) (j : Fin 3) :
    IsCompletelyPositive (F.comp transposeMap) ↔ IsCompletelyPositive (F.comp (R j)) := by
  constructor
  · intro h
    have hc := cp_comp _ (C j) h (cp_C j)
    convert hc using 1
    ext X i k
    change F (C j Xᵀ) i k = F (C j X)ᵀ i k
    rw [C_transpose]
  · intro h
    have hc := cp_comp _ (C j) h (cp_C j)
    convert hc using 1
    ext X i k
    change F Xᵀ i k = F (C j (C j X)ᵀ) i k
    rw [← C_transpose, C_invol]

private lemma cp_left_right_transpose (F : QMap) :
    IsCompletelyPositive (F.comp transposeMap) ↔
      IsCompletelyPositive (transposeMap.comp F) := by
  constructor
  · intro h
    have ht := cp_transpose _ h
    convert ht using 1
    ext X i k
    rfl
  · intro h
    have ht := cp_transpose _ h
    convert ht using 1
    ext X i k
    rfl

theorem solution (t lam : Bloch) (hPhi : CPT (canonical t lam)) :
    IsCompletelyPositive (transposeMap.comp ((canonical t lam).comp transposeMap)) ∧
    (∀ j, IsCompletelyPositive (canonical (Function.update t j (-t j)) lam)) ∧
    (IsCompletelyPositive ((canonical t lam).comp transposeMap) ↔
      ∀ j, IsCompletelyPositive (canonical t (Function.update lam j (-lam j)))) ∧
    (IsCompletelyPositive ((canonical t lam).comp transposeMap) ↔
      IsCompletelyPositive (transposeMap.comp (canonical t lam))) := by
  refine ⟨cp_transpose _ hPhi.2, ?_, ?_, cp_left_right_transpose _⟩
  · intro j
    rw [flip_t]
    exact cp_Rsandwich _ hPhi.2 j
  · constructor
    · intro h j
      rw [flip_lam]
      exact (cp_right_R_iff _ j).mp h
    · intro h
      have h1 := h 1
      simpa only [flip_lam,R_one] using h1
