-- Prove2me | solution 1 for TroppMatrixConcentration.ch8_joint_tensor_representation
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-07T14:55:01.050987+00:00
-- url     : https://prove2.me/submissions/2c047fcd-723d-47ab-9179-a7d2416ec82d

import Definitions.Def_TroppMatrixConcentration_ch8_joint_tensor
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder Kronecker
open Matrix
set_option autoImplicit false
noncomputable section
private def diagHom {n : Type*} [Fintype n] [DecidableEq n] :
    (n → ℂ) →⋆ₐ[ℂ] Matrix n n ℂ where
  toFun x := diagonal x
  map_one' := by simp
  map_mul' x y := by exact (diagonal_mul_diagonal x y).symm
  map_zero' := by simp
  map_add' x y := by simp [diagonal_add]
  commutes' r := by simp [algebraMap_eq_diagonal]
  map_star' x := by simp [star_eq_conjTranspose, diagonal_conjTranspose]

set_option backward.isDefEq.respectTransparency false in
private theorem cfc_diag {n : Type*} [Fintype n] [DecidableEq n]
    (f : ℝ → ℝ) (x : n → ℝ) :
    cfc f (diagonal (fun i => (x i : ℂ))) = diagonal (fun i => (f (x i) : ℂ)) := by
  let := IsStarNormal.instContinuousFunctionalCalculus (A := n → ℂ)
  let := IsSelfAdjoint.instContinuousFunctionalCalculus (A := n → ℂ)
  let z : n → ℂ := fun i => (x i : ℂ)
  have hx : IsSelfAdjoint z := by ext; simp [z]
  have hdiag : IsSelfAdjoint (diagHom z) := hx.map diagHom
  have hc : ContinuousOn f (spectrum ℝ z) := by
    rw [Pi.spectrum_eq]
    have heq : (⋃ i, spectrum ℝ (z i)) = Set.range x := by
      change (⋃ i, spectrum ℝ (algebraMap ℝ ℂ (x i))) = _
      simp only [spectrum.scalar_eq, Set.iUnion_singleton_eq_range]
    rw [heq]
    exact Set.Finite.continuousOn (Set.finite_range _) _
  have heq := (diagHom (n := n)).map_cfc (p := IsSelfAdjoint) (q := IsSelfAdjoint) f z hc
    (by change Continuous (fun z : n → ℂ => diagonal z); fun_prop) hx hdiag
  rw [cfc_map_pi (p := IsSelfAdjoint) (q := fun _ => IsSelfAdjoint) (S := ℂ) f z (by rwa [← Pi.spectrum_eq]) hx (fun i => by change star (x i : ℂ) = (x i : ℂ); simp)] at heq
  change diagonal (fun i => cfc f (algebraMap ℝ ℂ (x i))) = cfc f (diagonal (fun i => (x i : ℂ))) at heq
  simp only [cfc_algebraMap] at heq
  exact heq.symm

set_option backward.isDefEq.respectTransparency false in
private theorem cfc_diag_conj {n : Type*} [Fintype n] [DecidableEq n]
    (U : unitary (Matrix n n ℂ)) (f : ℝ → ℝ) (x : n → ℝ) :
    cfc f ((U : Matrix n n ℂ) * diagonal (fun i => (x i : ℂ)) * star (U : Matrix _ _ ℂ)) =
      (U : Matrix n n ℂ) * diagonal (fun i => (f (x i) : ℂ)) * star (U : Matrix _ _ ℂ) := by
  let φ := Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) U
  have hd : IsSelfAdjoint (diagonal (fun i => (x i : ℂ))) := by
    change (diagonal (fun i => (x i : ℂ)))ᴴ = _
    simp [diagonal_conjTranspose]
  have hc : ContinuousOn f (spectrum ℝ (diagonal (fun i => (x i : ℂ)))) := by
    rw [continuousOn_iff_continuous_domRestrict]
    fun_prop
  have heq := StarAlgHomClass.map_cfc (p := IsSelfAdjoint) (q := IsSelfAdjoint)
    φ f _ hc (by change Continuous (fun M : Matrix n n ℂ => (U : Matrix n n ℂ) * M * star (U : Matrix _ _ ℂ)); fun_prop) hd (hd.map φ)
  rw [cfc_diag] at heq
  exact heq.symm

private theorem conj_diag_mul {n : Type*} [Fintype n] [DecidableEq n]
    (U : unitary (Matrix n n ℂ)) (x y : n → ℝ) :
    ((U : Matrix n n ℂ) * diagonal (fun i => (x i : ℂ)) * star (U : Matrix _ _ ℂ)) *
      ((U : Matrix n n ℂ) * diagonal (fun i => (y i : ℂ)) * star (U : Matrix _ _ ℂ)) =
    (U : Matrix n n ℂ) * diagonal (fun i => ((x i * y i : ℝ) : ℂ)) * star (U : Matrix _ _ ℂ) := by
  change (Unitary.conjStarAlgAut ℂ _ U) _ * (Unitary.conjStarAlgAut ℂ _ U) _ = _
  rw [← map_mul, diagonal_mul_diagonal]
  simp only [Complex.ofReal_mul]
  rfl

open TroppMatrixConcentration
private theorem perspective_diag {n : ℕ} (U : unitary (Matrix (Fin n) (Fin n) ℂ))
    (a h : Fin n → ℝ) (ha : ∀ i, 0 < a i) (hh : ∀ i, 0 < h i) :
    ch8_perspective (fun x => -Real.log x)
      ((U : Matrix (Fin n) (Fin n) ℂ) * diagonal (fun i => (a i : ℂ)) * star (U : Matrix _ _ ℂ))
      ((U : Matrix (Fin n) (Fin n) ℂ) * diagonal (fun i => (h i : ℂ)) * star (U : Matrix _ _ ℂ)) =
    (U : Matrix (Fin n) (Fin n) ℂ) *
      diagonal (fun i => ((a i * (Real.log (a i) - Real.log (h i)) : ℝ) : ℂ)) * star (U : Matrix _ _ ℂ) := by
  simp only [ch8_perspective, ch8_matrixFunction, cfc_diag_conj, conj_diag_mul]
  congr 2
  apply congrArg diagonal
  funext i
  have hs := Real.sq_sqrt (ha i).le
  have hsn := Real.sqrt_pos.mpr (ha i)
  have heq : (Real.sqrt (a i))⁻¹ * h i * (Real.sqrt (a i))⁻¹ = h i / a i := by
    field_simp [hsn.ne', (ha i).ne']
    rw [hs, mul_comm]
  rw [heq, Real.log_div (hh i).ne' (ha i).ne']
  congr 1
  calc
    _ = (Real.sqrt (a i))^2 * (Real.log (a i) - Real.log (h i)) := by ring
    _ = _ := by rw [hs]

private def tensorU {d : ℕ} (U V : unitary (Matrix (Fin d) (Fin d) ℂ)) :
    unitary (Matrix (Fin (d*d)) (Fin (d*d)) ℂ) :=
  ⟨((U : Matrix _ _ ℂ) ⊗ₖ (V : Matrix _ _ ℂ)).submatrix
    finProdFinEquiv.symm finProdFinEquiv.symm, by
    have hu := kronecker_mem_unitary U.property V.property
    apply Matrix.mem_unitaryGroup_iff.mpr
    rw [star_eq_conjTranspose, conjTranspose_submatrix, submatrix_mul_equiv]
    rw [← star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff.mp hu, submatrix_one_equiv]⟩

private theorem tensor_conj {d : ℕ} (U V : unitary (Matrix (Fin d) (Fin d) ℂ))
    (a b : Fin d → ℝ) :
    (tensorU U V : Matrix _ _ ℂ) *
      diagonal (fun i => ((a (finProdFinEquiv.symm i).1 * b (finProdFinEquiv.symm i).2 : ℝ) : ℂ)) *
      star (tensorU U V : Matrix _ _ ℂ) =
    (((U : Matrix _ _ ℂ) * diagonal (fun j => (a j : ℂ)) * star (U : Matrix _ _ ℂ)) ⊗ₖ
      ((V : Matrix _ _ ℂ) * diagonal (fun j => (b j : ℂ)) * star (V : Matrix _ _ ℂ))).submatrix
      finProdFinEquiv.symm finProdFinEquiv.symm := by
  simp only [tensorU, star_eq_conjTranspose, conjTranspose_submatrix, conjTranspose_kronecker]
  rw [mul_kronecker_mul, mul_kronecker_mul, ← submatrix_mul_equiv _ _ _ finProdFinEquiv.symm,
    ← submatrix_mul_equiv _ _ _ finProdFinEquiv.symm]
  congr 2
  rw [diagonal_kronecker_diagonal]
  rw [submatrix_diagonal_equiv]
  simp only [Function.comp_def, Complex.ofReal_mul]


private theorem conj_diag_sub {n : Type*} [Fintype n] [DecidableEq n]
    (U : unitary (Matrix n n ℂ)) (x y : n → ℝ) :
    ((U : Matrix n n ℂ) * diagonal (fun i => (x i : ℂ)) * star (U : Matrix n n ℂ)) -
      ((U : Matrix n n ℂ) * diagonal (fun i => (y i : ℂ)) * star (U : Matrix n n ℂ)) =
    (U : Matrix n n ℂ) * diagonal (fun i => ((x i - y i : ℝ) : ℂ)) * star (U : Matrix n n ℂ) := by
  simp only [← sub_mul, ← mul_sub, ← diagonal_sub, Complex.ofReal_sub]

private theorem perspective_tensor_diag {d : ℕ} (U V : unitary (Matrix (Fin d) (Fin d) ℂ))
    (a h : Fin d → ℝ) (ha : ∀ i, 0 < a i) (hh : ∀ i, 0 < h i) :
    ch8_perspective (fun x => -Real.log x)
      ((((U : Matrix _ _ ℂ) * diagonal (fun i => (a i : ℂ)) * star (U : Matrix _ _ ℂ)) ⊗ₖ 1).submatrix
        finProdFinEquiv.symm finProdFinEquiv.symm)
      ((1 ⊗ₖ ((V : Matrix _ _ ℂ) * diagonal (fun i => (h i : ℂ)) * star (V : Matrix _ _ ℂ))).submatrix
        finProdFinEquiv.symm finProdFinEquiv.symm) =
    ((((U : Matrix _ _ ℂ) * diagonal (fun i => ((a i * Real.log (a i) : ℝ) : ℂ)) * star (U : Matrix _ _ ℂ)) ⊗ₖ 1) -
       (((U : Matrix _ _ ℂ) * diagonal (fun i => (a i : ℂ)) * star (U : Matrix _ _ ℂ)) ⊗ₖ
        ((V : Matrix _ _ ℂ) * diagonal (fun i => (Real.log (h i) : ℂ)) * star (V : Matrix _ _ ℂ)))).submatrix
          finProdFinEquiv.symm finProdFinEquiv.symm := by
  have hu : (U : Matrix (Fin d) (Fin d) ℂ) * diagonal (fun _ => ((1 : ℝ) : ℂ)) * star (U : Matrix _ _ ℂ) = 1 := by simp
  have hv : (V : Matrix (Fin d) (Fin d) ℂ) * diagonal (fun _ => ((1 : ℝ) : ℂ)) * star (V : Matrix _ _ ℂ) = 1 := by simp
  have he1 := tensor_conj U V a (fun _ => 1)
  have he2 := tensor_conj U V (fun _ => 1) h
  have he3 := tensor_conj U V (fun i => a i * Real.log (a i)) (fun _ => 1)
  have he4 := tensor_conj U V a (fun i => Real.log (h i))
  simp only [mul_one, hu, hv, one_mul] at he1 he2 he3
  rw [← he1, ← he2, perspective_diag (tensorU U V) _ _
    (fun i => ha _) (fun i => hh _), submatrix_sub, Pi.sub_apply, Pi.sub_apply, ← he3, ← he4, conj_diag_sub]
  congr 2
  apply congrArg diagonal
  funext i
  congr 1
  ring

set_option backward.isDefEq.respectTransparency false in
private theorem perspective_tensor {d : ℕ}
    (A B : Matrix (Fin d) (Fin d) ℂ) (hA : A.PosDef) (hB : B.PosDef) :
    ch8_perspective (fun x => -Real.log x)
      ((A ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)).submatrix finProdFinEquiv.symm finProdFinEquiv.symm)
      (((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ B).submatrix finProdFinEquiv.symm finProdFinEquiv.symm) =
    (((A * matrixLog A) ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) - (A ⊗ₖ matrixLog B)).submatrix
      finProdFinEquiv.symm finProdFinEquiv.symm := by
  have he := perspective_tensor_diag hA.1.eigenvectorUnitary hB.1.eigenvectorUnitary
    hA.1.eigenvalues hB.1.eigenvalues hA.eigenvalues_pos hB.eigenvalues_pos
  have ha := hA.1.spectral_theorem
  have hb := hB.1.spectral_theorem
  have hla := hA.1.cfc_eq Real.log
  have hlb := hB.1.cfc_eq Real.log
  simp only [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Function.comp_def, RCLike.ofReal_eq_complex_ofReal] at ha hb hla hlb
  change cfc Real.log A = _ at hla
  have hal : A * matrixLog A =
      (hA.1.eigenvectorUnitary : Matrix _ _ ℂ) *
        diagonal (fun i => ((hA.1.eigenvalues i * Real.log (hA.1.eigenvalues i) : ℝ) : ℂ)) *
        star (hA.1.eigenvectorUnitary : Matrix _ _ ℂ) := by
    rw [matrixLog, hla]
    conv_lhs => lhs; rw [ha]
    exact conj_diag_mul hA.1.eigenvectorUnitary _ _
  simpa only [← ha, ← hb, ← hal, ← hlb, matrixLog] using he

private lemma ch8_joint_tensor_contraction {d : ℕ} (A H : Matrix (Fin d) (Fin d) ℂ) :
    ch8_joint_eval ((A ⊗ₖ H.transpose).submatrix finProdFinEquiv.symm finProdFinEquiv.symm) =
      (Matrix.trace (A * H)).re := by
  unfold ch8_joint_eval
  congr 1
  simp only [dotProduct, Matrix.mulVec, Matrix.submatrix_apply]
  rw [← Equiv.sum_comp finProdFinEquiv]
  simp only [finProdFinEquiv.symm_apply_apply, Fintype.sum_prod_type]
  simp [ch8_joint_vec, Matrix.kroneckerMap, Matrix.trace, Matrix.mul_apply, Matrix.diag]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Equiv.sum_comp finProdFinEquiv]
  simp only [Fintype.sum_prod_type]
  change (∑ x, ∑ y, if (finProdFinEquiv.symm (finProdFinEquiv (x,y))).1 =
    (finProdFinEquiv.symm (finProdFinEquiv (x,y))).2 then
    A i (finProdFinEquiv.symm (finProdFinEquiv (x,y))).1 *
    H (finProdFinEquiv.symm (finProdFinEquiv (x,y))).2 i else 0) = _
  simp


private theorem eval_sub {d : ℕ} (M N : Matrix (Fin (d*d)) (Fin (d*d)) ℂ) :
    ch8_joint_eval (M - N) = ch8_joint_eval M - ch8_joint_eval N := by
  simp [ch8_joint_eval, Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re]

private theorem finish {d : ℕ} [NeZero d]
    (A H : Matrix (Fin d) (Fin d) ℂ) (hA : A.PosDef) (hH : H.PosDef)
    (ht : matrixLog H.transpose = (matrixLog H).transpose) :
    ch8_relativeEntropy A H =
      ch8_joint_eval (ch8_perspective (fun x => -Real.log x)
        (ch8_joint_left A) (ch8_joint_right H)) - (Matrix.trace (A - H)).re := by
  have he := perspective_tensor A H.transpose hA hH.transpose
  unfold ch8_joint_left ch8_joint_right
  rw [he, ht]
  have hsub :
      (((A * matrixLog A) ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) - (A ⊗ₖ (matrixLog H).transpose)).submatrix
        finProdFinEquiv.symm finProdFinEquiv.symm =
      (((A * matrixLog A) ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)).submatrix
        finProdFinEquiv.symm finProdFinEquiv.symm) -
      ((A ⊗ₖ (matrixLog H).transpose).submatrix finProdFinEquiv.symm finProdFinEquiv.symm) := rfl
  rw [hsub, eval_sub, ch8_joint_tensor_contraction]
  have hc := ch8_joint_tensor_contraction (A * matrixLog A) (1 : Matrix (Fin d) (Fin d) ℂ)
  simp only [transpose_one, mul_one] at hc
  rw [hc]
  simp [ch8_relativeEntropy, mul_sub, Matrix.trace_sub, Complex.sub_re]

set_option maxHeartbeats 1000000 in
private theorem cfc_transpose {d : ℕ} (H : Matrix (Fin d) (Fin d) ℂ)
    (hH : H.IsHermitian) (f : ℝ → ℝ) :
    cfc f H.transpose = (cfc f H).transpose := by
  let U := hH.eigenvectorUnitary
  let V := Matrix.UnitaryGroup.map_star U
  have ht (x : Fin d → ℝ) :
      ((U : Matrix (Fin d) (Fin d) ℂ) * diagonal (fun i => (x i : ℂ)) * star (U : Matrix (Fin d) (Fin d) ℂ)).transpose =
        (V : Matrix (Fin d) (Fin d) ℂ) * diagonal (fun i => (x i : ℂ)) * star (V : Matrix (Fin d) (Fin d) ℂ) := by
    simp only [transpose_mul, diagonal_transpose, star_eq_conjTranspose]
    rw [Matrix.mul_assoc]
    congr 2
    change (U : Matrix (Fin d) (Fin d) ℂ).transpose = ((U : Matrix (Fin d) (Fin d) ℂ).map star).conjTranspose
    ext i j
    simp
  have hs := hH.spectral_theorem
  simp only [Unitary.conjStarAlgAut_apply, Function.comp_def, RCLike.ofReal_eq_complex_ofReal] at hs
  rw [hs, ht, cfc_diag_conj, cfc_diag_conj, ht]


theorem solution {d : ℕ} [NeZero d]
    (A H : Matrix (Fin d) (Fin d) ℂ) (hA : A.PosDef) (hH : H.PosDef) :
    ch8_relativeEntropy A H =
      ch8_joint_eval (ch8_perspective (fun x => -Real.log x)
        (ch8_joint_left A) (ch8_joint_right H)) - (Matrix.trace (A - H)).re := by
  exact finish A H hA hH (cfc_transpose H hH.1 Real.log)
