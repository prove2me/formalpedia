-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P08.planarChannels
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T03:21:45.669847+00:00
-- url     : https://prove2.me/submissions/79fbc889-d924-4578-bf5e-0b10a91229c2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P08_theorem2
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

private def axisMatrix (j : Fin 3) : Matrix Bool Bool ℂ := ![pauliZ,1,pauliX] j

private lemma planar_complement_cp (t lam : Bloch) (j : Fin 3) (hz : lam j = 0)
    (h : IsCompletelyPositive (canonical t lam)) :
    IsCompletelyPositive (canonical (-t) (-lam)) := by
  have hc := cp_comp (sandwich pauliY)
    ((transposeMap.comp ((canonical t lam).comp transposeMap)).comp (sandwich (axisMatrix j)))
    (cp_sandwich _) (cp_comp _ _ (cp_transpose _ h) (cp_sandwich _))
  have he : canonical (-t) (-lam) = (sandwich pauliY).comp
      ((transposeMap.comp ((canonical t lam).comp transposeMap)).comp (sandwich (axisMatrix j))) := by
    fin_cases j <;> ext X i k <;> cases i <;> cases k <;>
      simp [canonical_entries,axisMatrix,sandwich,pauliX,pauliY,pauliZ,
        Matrix.mul_apply,Matrix.conjTranspose_apply] <;>
      ring_nf <;> simp_all [Complex.I_sq] <;> ring
  rw [he]
  exact hc

private lemma bell_entries (i j k l : Bool) :
    pureDensity bell (i,j) (k,l) = if i = j ∧ k = l then (1/2 : ℂ) else 0 := by
  have hr : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (1/2 : ℝ) := by
    rw [← mul_inv, ← pow_two, Real.sq_sqrt (by norm_num)]
    norm_num
  cases i <;> cases j <;> cases k <;> cases l <;>
    norm_num [pureDensity,bell,finiteMaxEntangled] <;> simpa only [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_div,
      Complex.ofReal_one, Complex.ofReal_ofNat] using congrArg Complex.ofReal hr

private lemma choi_complement (t lam : Bloch) :
    (1/2 : ℂ) • (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ) - choiState (canonical t lam) =
      choiState (canonical (-t) (-lam)) := by
  ext ⟨i,j⟩ ⟨k,l⟩
  cases i <;> cases j <;> cases k <;> cases l <;>
    norm_num [choiState,idTensorSuperop,canonical_entries,bell_entries,Matrix.one_apply] <;> ring

private lemma choi_positive (Phi : QMap) (h : IsCompletelyPositive Phi) :
    (choiState Phi).PosSemidef := by
  have hb : (pureDensity bell).PosSemidef := by
    exact Matrix.posSemidef_vecMulVec_self_star _
  have hp := h 2
    ((pureDensity bell).submatrix (fun p : Fin 2 × Bool => (finTwoEquiv p.1,p.2))
      (fun p : Fin 2 × Bool => (finTwoEquiv p.1,p.2)))
    (hb.submatrix (fun p : Fin 2 × Bool => (finTwoEquiv p.1,p.2)))
  have hf := hp.submatrix (fun p : Bool × Bool => (finTwoEquiv.symm p.1,p.2))
  convert hf using 1
  ext p q
  simp [choiState,idTensorSuperop]

theorem solution (t lam : Bloch) (hPhi : CPT (canonical t lam))
    (hzero : ∃ j, lam j = 0) : EBT (canonical t lam) := by
  apply (theorem2 _ hPhi).mpr
  rw [choi_complement]
  obtain ⟨j,hj⟩ := hzero
  exact choi_positive _ (planar_complement_cp t lam j hj hPhi.2)

#print axioms solution
